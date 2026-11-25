||| Regression and property tests for the pure UTF-8 SipHash implementation.
module SipHash

import Data.Hashable.SipHash
import Data.Hashable.SipHashV2
import Hedgehog

%default total

||| A known-answer test for the fixed, zero-key SipHash-2-4 API.
vector : String -> Bits64 -> Property
vector input expected = property $ do
  siphashString input === expected

||| For ASCII, the UTF-8 implementation must match the byte-stream API.
propASCIIEquivalence : Property
propASCIIEquivalence = property $ do
  str <- forAll $ string (linear 0 128) ascii
  let bytes : List Bits8
      bytes = map (cast . ord) (unpack str)
  siphashString str === hashBytes bytes

export
suite : Group
suite = MkGroup "SipHash (pure UTF-8)"
  [ ("empty string", vector "" 0x1e924b9d737700d7)
  , ("one byte", vector "a" 0x96c20860cd93a249)
  , ("three bytes", vector "abc" 0x3fc884964770eede)
  , ("eight bytes", vector "abcdefgh" 0xe65ba172cce22193)
  , ("nine bytes", vector "abcdefghi" 0x53273c4a18d0258c)
  , ("embedded NUL", vector "a\0b" 0xf59b60f31b14f7ba)
  , ("trailing NUL", vector "abcdefgh\0" 0x6c6b422ce396029a)
  , ("UTF-8 two-byte character", vector "é" 0x57e141910cde6118)
  , ("UTF-8 three-byte character", vector "€" 0xdc4687c89a2843d1)
  , ("UTF-8 four-byte character", vector "😀" 0xcf04b86667d305b4)
  , ("UTF-8 crossing block", vector "abcdefgé" 0xc2783ce13ec003fd)
  , ("mixed UTF-8", vector "hello😀" 0x9015ac380898b6af)
  , ("ASCII byte equivalence", propASCIIEquivalence)
  ]
