//! Parallel iterators over string data: `par_chars`, `par_char_indices`,
//! `par_bytes`, `par_lines`, `par_split_whitespace`.
//!
//! Strings can't be split at arbitrary byte positions, so these are
//! *unindexed* iterators whose producers split near the middle and then
//! scan forward to the nearest safe boundary (char boundary, newline, or
//! whitespace, respectively).

use crate::iter::plumbing::{bridge_unindexed, Folder, UnindexedConsumer, UnindexedProducer};
use crate::iter::ParallelIterator;

/// Parallel extensions for `str`.
pub trait ParallelString {
    /// Returns the string (implementation detail).
    fn as_parallel_string(&self) -> &str;

    /// Parallel iterator over the characters.
    fn par_chars(&self) -> Chars<'_> {
        Chars {
            chars: self.as_parallel_string(),
        }
    }

    /// Parallel iterator over `(byte index, char)` pairs.
    fn par_char_indices(&self) -> CharIndices<'_> {
        CharIndices {
            chars: self.as_parallel_string(),
        }
    }

    /// Parallel iterator over the bytes (indexed: delegates to the byte
    /// slice).
    fn par_bytes(&self) -> crate::iter::Copied<crate::slice::Iter<'_, u8>> {
        use crate::iter::IntoParallelIterator;
        self.as_parallel_string()
            .as_bytes()
            .into_par_iter()
            .copied()
    }

    /// Parallel iterator over the lines, like [`str::lines`].
    fn par_lines(&self) -> Lines<'_> {
        Lines(self.as_parallel_string())
    }

    /// Parallel iterator over whitespace-separated words, like
    /// [`str::split_whitespace`].
    fn par_split_whitespace(&self) -> SplitWhitespace<'_> {
        SplitWhitespace(self.as_parallel_string())
    }
}

impl ParallelString for str {
    #[inline]
    fn as_parallel_string(&self) -> &str {
        self
    }
}

/// Finds the char boundary closest to the middle of `chars`.
#[inline]
fn find_char_midpoint(chars: &str) -> usize {
    let mid = chars.len() / 2;
    // We want to split near the midpoint, but we need to find an actual
    // character boundary. So we look at the raw bytes: the split point
    // is the first byte at or after the midpoint that isn't a UTF-8
    // continuation byte.
    chars.as_bytes()[mid..]
        .iter()
        .position(|&b| (b as i8) >= -0x40)
        .map(|i| mid + i)
        .unwrap_or(chars.len())
}

// //////////////////////////////////////////////////////////////////////
// Chars

/// Parallel iterator over a string's characters.
#[derive(Debug, Clone)]
pub struct Chars<'ch> {
    chars: &'ch str,
}

impl<'ch> ParallelIterator for Chars<'ch> {
    type Item = char;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge_unindexed(CharsProducer { chars: self.chars }, consumer)
    }
}

struct CharsProducer<'ch> {
    chars: &'ch str,
}

impl<'ch> UnindexedProducer for CharsProducer<'ch> {
    type Item = char;

    fn split(self) -> (Self, Option<Self>) {
        let index = find_char_midpoint(self.chars);
        if index > 0 && index < self.chars.len() {
            let (left, right) = self.chars.split_at(index);
            (
                CharsProducer { chars: left },
                Some(CharsProducer { chars: right }),
            )
        } else {
            (self, None)
        }
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        folder.consume_iter(self.chars.chars())
    }
}

// //////////////////////////////////////////////////////////////////////
// CharIndices

/// Parallel iterator over a string's characters and their byte offsets.
#[derive(Debug, Clone)]
pub struct CharIndices<'ch> {
    chars: &'ch str,
}

impl<'ch> ParallelIterator for CharIndices<'ch> {
    type Item = (usize, char);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge_unindexed(
            CharIndicesProducer {
                index: 0,
                chars: self.chars,
            },
            consumer,
        )
    }
}

struct CharIndicesProducer<'ch> {
    index: usize,
    chars: &'ch str,
}

impl<'ch> UnindexedProducer for CharIndicesProducer<'ch> {
    type Item = (usize, char);

    fn split(self) -> (Self, Option<Self>) {
        let index = find_char_midpoint(self.chars);
        if index > 0 && index < self.chars.len() {
            let (left, right) = self.chars.split_at(index);
            let base = self.index;
            (
                CharIndicesProducer {
                    index: base,
                    chars: left,
                },
                Some(CharIndicesProducer {
                    index: base + index,
                    chars: right,
                }),
            )
        } else {
            (self, None)
        }
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        let base = self.index;
        folder.consume_iter(self.chars.char_indices().map(|(i, c)| (base + i, c)))
    }
}

// //////////////////////////////////////////////////////////////////////
// Lines

/// Parallel iterator over a string's lines.
#[derive(Debug, Clone)]
pub struct Lines<'ch>(&'ch str);

impl<'ch> ParallelIterator for Lines<'ch> {
    type Item = &'ch str;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge_unindexed(LinesProducer(self.0), consumer)
    }
}

struct LinesProducer<'ch>(&'ch str);

impl<'ch> UnindexedProducer for LinesProducer<'ch> {
    type Item = &'ch str;

    fn split(self) -> (Self, Option<Self>) {
        // Split *after* a newline at-or-after the midpoint: both sides
        // then contain only whole terminated lines. Searching raw bytes
        // for b'\n' sidesteps char-boundary concerns (a '\n' byte is
        // always a boundary in UTF-8).
        let mid = self.0.len() / 2;
        match self.0.as_bytes()[mid..].iter().position(|&b| b == b'\n') {
            Some(offset) => {
                let index = mid + offset;
                // Left keeps its trailing '\n' so empty lines survive
                // (both sides fold with `split_terminator`).
                let left = &self.0[..index + 1];
                let right = &self.0[index + 1..];
                (LinesProducer(left), Some(LinesProducer(right)))
            }
            None => (self, None),
        }
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        // `str::lines()` semantics, but implemented so that they hold for
        // *chunks* too: split on '\n' terminators (which we preserved at
        // split points) and strip one trailing '\r' per line.
        folder.consume_iter(
            self.0
                .split_terminator('\n')
                .map(|line| line.strip_suffix('\r').unwrap_or(line)),
        )
    }
}

// //////////////////////////////////////////////////////////////////////
// SplitWhitespace

/// Parallel iterator over whitespace-separated words.
#[derive(Debug, Clone)]
pub struct SplitWhitespace<'ch>(&'ch str);

impl<'ch> ParallelIterator for SplitWhitespace<'ch> {
    type Item = &'ch str;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge_unindexed(SplitWhitespaceProducer(self.0), consumer)
    }
}

struct SplitWhitespaceProducer<'ch>(&'ch str);

impl<'ch> UnindexedProducer for SplitWhitespaceProducer<'ch> {
    type Item = &'ch str;

    fn split(self) -> (Self, Option<Self>) {
        // Split at a whitespace char at-or-after the midpoint: the word
        // spanning the midpoint stays whole on the left side.
        let mid = self.0.len() / 2;
        let s = &self.0[find_char_midpoint_at(self.0, mid)..];
        match s.find(char::is_whitespace) {
            Some(offset) => {
                let index = self.0.len() - s.len() + offset;
                // `index` points at a whitespace char; skip it.
                let ws_len = self.0[index..].chars().next().map_or(0, char::len_utf8);
                let left = &self.0[..index];
                let right = &self.0[index + ws_len..];
                (
                    SplitWhitespaceProducer(left),
                    Some(SplitWhitespaceProducer(right)),
                )
            }
            None => (self, None),
        }
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        folder.consume_iter(self.0.split_whitespace())
    }
}

/// Rounds `i` up to the nearest char boundary of `s`.
#[inline]
fn find_char_midpoint_at(s: &str, i: usize) -> usize {
    s.as_bytes()[i..]
        .iter()
        .position(|&b| (b as i8) >= -0x40)
        .map(|off| i + off)
        .unwrap_or(s.len())
}
