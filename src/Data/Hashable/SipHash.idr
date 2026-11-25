||| SipHash-2-4 implementation using pure, linearly scoped mutable state.
module Data.Hashable.SipHash

import Data.Linear.Ref1

%default total

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

||| Number of SipHash compression rounds.
%inline
CROUNDS : Nat
CROUNDS = 2

||| Number of SipHash finalization rounds.
%inline
DROUNDS : Nat
DROUNDS = 4

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------

||| Internal SipHash state.
record State where
  constructor MkState
  v0 : Bits64
  v1 : Bits64
  v2 : Bits64
  v3 : Bits64

||| Initial SipHash state for the fixed zero key.
%inline
initialState : State
initialState = MkState 0x736f6d6570736575
                       0x646f72616e646f6d
                       0x6c7967656e657261
                       0x7465646279746573

--------------------------------------------------------------------------------
-- Pending message state
--------------------------------------------------------------------------------

||| Bytes waiting to form a complete 64-bit message word.
|||
||| `tail` contains between zero and seven bytes.
||| `used` is the number of bytes currently stored in `tail`.
||| `bytes` is the total number of UTF-8 bytes processed.
private
record Pending where
  constructor MkPending
  tail  : Bits64
  used  : Nat
  bytes : Bits64

||| Initial pending message state.
%inline
initialPending : Pending
initialPending = MkPending 0 0 0

--------------------------------------------------------------------------------
-- Bitwise operations
--------------------------------------------------------------------------------

%inline
shl : Bits64 -> Bits64 -> Bits64
shl = prim__shl_Bits64

%inline
shr : Bits64 -> Bits64 -> Bits64
shr = prim__shr_Bits64

%inline
bor : Bits64 -> Bits64 -> Bits64
bor = prim__or_Bits64

%inline
xor : Bits64 -> Bits64 -> Bits64
xor = prim__xor_Bits64

%inline
and64 : Bits64 -> Bits64 -> Bits64
and64 = prim__and_Bits64

||| Rotate a 64-bit word to the left.
%inline
rotl : Bits64 -> Bits64 -> Bits64
rotl x b =
  (x `shl` b) `bor` (x `shr` (64 - b))

--------------------------------------------------------------------------------
-- SipRound
--------------------------------------------------------------------------------

||| Perform one SipHash round.
|||
||| This function is pure and does not mutate the underlying state.
%inline
sipRound : State -> State
sipRound (MkState v0 v1 v2 v3) =
  let v0 = v0 + v1
      v1 = v1 `rotl` 13
      v1 = v1 `xor` v0
      v0 = v0 `rotl` 32

      v2 = v2 + v3
      v3 = v3 `rotl` 16
      v3 = v3 `xor` v2

      v0 = v0 + v3
      v3 = v3 `rotl` 21
      v3 = v3 `xor` v0

      v2 = v2 + v1
      v1 = v1 `rotl` 17
      v1 = v1 `xor` v2
      v2 = v2 `rotl` 32

   in MkState v0 v1 v2 v3

||| Apply a SipHash round a specified number of times.
%inline
sipRounds : Nat -> State -> State
sipRounds Z st     = st
sipRounds (S k) st = sipRounds k (sipRound st)

--------------------------------------------------------------------------------
-- Compression
--------------------------------------------------------------------------------

||| Compress one complete 64-bit message word.
|||
||| SipHash-2-4 performs two compression rounds per message block.
|||
||| The compression sequence is:
|||
|||   v3 ^= m
|||   SIPROUND
|||   SIPROUND
|||   v0 ^= m
|||
||| All mutations are scoped to the supplied linear reference.
%inline
siphashCompress : Ref s State -> Bits64 -> F1' s
siphashCompress r m =
  mod1 r $ \st =>
    let st = { v3 $= (`xor` m) } st
        st = sipRounds CROUNDS st
     in { v0 $= (`xor` m) } st

--------------------------------------------------------------------------------
-- Byte processing
--------------------------------------------------------------------------------

||| Add one byte to the SipHash computation.
|||
||| Bytes are accumulated in little-endian order.
||| Every complete eight-byte word is immediately compressed.
|||
||| The pending state contains at most seven bytes between calls.
%inline
addByte :
     Ref s State
  -> Bits8
  -> Pending
  -> F1 s Pending
addByte r byte p t =
  let shift : Bits64
      shift = cast (8 * p.used)

      word : Bits64
      word = p.tail `bor` (cast byte `shl` shift)

      bytes : Bits64
      bytes = p.bytes + 1

   in if p.used == 7
        then
          let _ # t := siphashCompress r word t
           in MkPending 0 0 bytes # t
        else
          MkPending word (S p.used) bytes # t

--------------------------------------------------------------------------------
-- UTF-8 encoding
--------------------------------------------------------------------------------

||| Encode a Unicode character as UTF-8 and feed its bytes directly
||| into the SipHash computation.
|||
||| No intermediate byte buffer is allocated.
|||
||| Assumes the input character represents a valid Unicode scalar
||| value (U+0000 through U+10FFFF, excluding surrogates).
emitChar :
     Ref s State
  -> Char
  -> Pending
  -> F1 s Pending
emitChar r c p t =
  let cp : Bits64
      cp = cast (ord c)
   in if cp < 0x80
        then
          addByte r (cast cp) p t
      else if cp < 0x800
        then
          let b0 : Bits8
              b0 = cast (0xc0 `bor` (cp `shr` 6))
              b1 : Bits8
              b1 = cast (0x80 `bor` (cp `and64` 0x3f))
              p # t := addByte r b0 p t
           in addByte r b1 p t
      else if cp < 0x10000
        then
          let b0 : Bits8
              b0 = cast (0xe0 `bor` (cp `shr` 12))
              b1 : Bits8
              b1 = cast
                (0x80 `bor` ((cp `shr` 6) `and64` 0x3f))
              b2 : Bits8
              b2 = cast (0x80 `bor` (cp `and64` 0x3f))
              p # t := addByte r b0 p t
              p # t := addByte r b1 p t
           in addByte r b2 p t
      else
        let b0 : Bits8
            b0 = cast (0xf0 `bor` (cp `shr` 18))
            b1 : Bits8
            b1 = cast
              (0x80 `bor` ((cp `shr` 12) `and64` 0x3f))
            b2 : Bits8
            b2 = cast
              (0x80 `bor` ((cp `shr` 6) `and64` 0x3f))
            b3 : Bits8
            b3 = cast (0x80 `bor` (cp `and64` 0x3f))
            p # t := addByte r b0 p t
            p # t := addByte r b1 p t
            p # t := addByte r b2 p t
         in addByte r b3 p t

--------------------------------------------------------------------------------
-- String processing
--------------------------------------------------------------------------------

||| Process a list of Unicode characters as UTF-8.
|||
||| Every character is encoded incrementally and incorporated into
||| the SipHash computation.
|||
||| Recursion is structural, so no termination assertions are needed.
hashChars :
     Ref s State
  -> List Char
  -> Pending
  -> F1 s Pending
hashChars r []        p t =
  p # t
hashChars r (c :: cs) p t =
  let p # t := emitChar r c p t
   in hashChars r cs p t

--------------------------------------------------------------------------------
-- Finalization
--------------------------------------------------------------------------------

||| Finalize SipHash-2-4.
|||
||| The final message word contains any remaining bytes and the
||| message length modulo 256 in its most significant byte.
|||
||| The finalization sequence is:
|||
|||   v3 ^= b
|||   SIPROUND
|||   SIPROUND
|||   v0 ^= b
|||   v2 ^= 0xff
|||   SIPROUND
|||   SIPROUND
|||   SIPROUND
|||   SIPROUND
|||
|||   result = v0 ^ v1 ^ v2 ^ v3
%inline
siphashFinalize :
     Ref s State
  -> Pending
  -> F1 s Bits64
siphashFinalize r p t =
  let b                         : Bits64
      b                         := p.tail `bor` (p.bytes `shl` 56)
      _                     # t := siphashCompress r b t
      _                     # t := mod1 r ({ v2 $= (`xor` 0xff) }) t
      _                     # t := mod1 r (sipRounds DROUNDS) t
      (MkState v0 v1 v2 v3) # t := read1 r t
   in ((v0 `xor` v1) `xor` (v2 `xor` v3)) # t

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

||| Compute SipHash-2-4 for a UTF-8 string.
|||
||| Uses the fixed zero key for compatibility with the existing API.
|||
||| The computation is pure, with mutable state managed by ref1.
|||
||| No unsafePerformIO, IORef, or intermediate byte buffer is used.
export
siphashString : String -> Bits64
siphashString str =
  run1 $ \t =>
    let r # t := ref1 initialState t
        p # t := hashChars r (unpack str) initialPending t
     in siphashFinalize r p t
