//! Small helpers for formatting into fixed buffers with `core::fmt`.

/// A [`core::fmt::Write`] that fills a byte slice and silently truncates.
pub struct SliceWriter<'a> {
    buf: &'a mut [u8],
    len: usize,
}

impl<'a> SliceWriter<'a> {
    /// Creates a writer over `buf`, keeping one byte spare for a NUL.
    pub fn new(buf: &'a mut [u8]) -> Self {
        SliceWriter { buf, len: 0 }
    }

    /// Number of bytes written so far.
    pub fn len(&self) -> usize {
        self.len
    }

    /// True if nothing has been written.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl core::fmt::Write for SliceWriter<'_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let room = self.buf.len().saturating_sub(1).saturating_sub(self.len);
        let n = s.len().min(room);
        self.buf[self.len..self.len + n].copy_from_slice(&s.as_bytes()[..n]);
        self.len += n;
        Ok(())
    }
}
