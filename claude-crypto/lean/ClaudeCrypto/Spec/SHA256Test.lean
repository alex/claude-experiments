import ClaudeCrypto.Spec.SHA256

/-! Known-answer tests for the specification (FIPS 180-4 examples / NIST CAVP).
These are checked by the kernel (`decide`) when this file is compiled. -/

namespace CC.Spec.SHA256.Test
open CC.Spec.SHA256

def bytesOfString (s : String) : List (BitVec 8) := s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

def hex (bs : List (BitVec 8)) : String :=
  String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

-- FIPS 180-4 example "abc"
example : hex (sha256 (bytesOfString "abc")) =
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by native_decide
-- empty message
example : hex (sha256 []) =
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by native_decide
-- FIPS 180-4 two-block example
example : hex (sha256 (bytesOfString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) =
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by native_decide

end CC.Spec.SHA256.Test
