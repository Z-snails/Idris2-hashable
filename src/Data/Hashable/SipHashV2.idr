||| Incremental SipHash-2-4 implementation.
module Data.Hashable.SipHashV2

import Data.Buffer
import Data.Linear.Ref1
import Data.Nat

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
-- Hash state
--------------------------------------------------------------------------------

||| Internal SipHash state.
record HashState where
  constructor MkST
  v0 : Bits64
  v1 : Bits64
  v2 : Bits64
  v3 : Bits64

||| Initial SipHash state for the fixed zero key.
%inline
initHashState : HashState
initHashState = MkST 0x736f6d6570736575
                     0x646f72616e646f6d
                     0x6c7967656e657261
                     0x7465646279746573

--------------------------------------------------------------------------------
-- Partial hash state
--------------------------------------------------------------------------------

||| Incremental SipHash state.
|||
||| `tail` contains pending message bytes in little-endian order.
||| `index` is the number of occupied bits in `tail`.
||| `length` is the total number of bytes processed.
||| `hst` contains the compressed SipHash state.
|||
||| Valid states maintain these invariants:
|||
||| - index is one of 0, 8, 16, 24, 32, 40, 48, or 56.
||| - tail contains only the pending message bytes.
||| - length counts actual bytes, including pending bytes.
export
record PartialHash where
  constructor MkPartial
  tail   : Bits64
  index  : Bits64
  length : Bits64
  hst    : HashState

||| Initial incremental hashing state.
|||
||| Uses the fixed zero key.
export %inline
initPartial : PartialHash
initPartial = MkPartial 0 0 0 initHashState

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

%inline
shr16 : Bits16 -> Bits16 -> Bits16
shr16 = prim__shr_Bits16

%inline
shr32 : Bits32 -> Bits32 -> Bits32
shr32 = prim__shr_Bits32

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
||| This is a pure state transformation.
%inline
compress : HashState -> HashState
compress (MkST v0 v1 v2 v3) =
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

   in MkST v0 v1 v2 v3

||| Apply a state transformation a specified number of times.
%inline
repeat : Nat -> (a -> a) -> a -> a
repeat Z f x = x
repeat (S k) f x = repeat k f (f x)

--------------------------------------------------------------------------------
-- Compression
--------------------------------------------------------------------------------

||| Compress one complete 64-bit message word.
|||
||| The compression sequence is:
|||
|||   v3 ^= m
|||   SIPROUND
|||   SIPROUND
|||   v0 ^= m
%inline
hashBits64 : HashState -> Bits64 -> HashState
hashBits64 st m =
  let st = { v3 $= (`xor` m) } st
      st = repeat CROUNDS compress st
   in { v0 $= (`xor` m) } st

--------------------------------------------------------------------------------
-- Incremental byte processing
--------------------------------------------------------------------------------

||| Add one byte to an incremental SipHash computation.
|||
||| Bytes are accumulated in little-endian order.
||| A complete eight-byte word is compressed immediately.
|||
||| Every call increases the message length by exactly one byte.
export
%inline
addBits8 : PartialHash -> Bits8 -> PartialHash
addBits8 (MkPartial tail index len hs) x =
  let word : Bits64
      word = tail `bor` (cast x `shl` index)
      len' : Bits64
      len' = len + 1
   in if index == 56
        then
          MkPartial 0 0 len' (hashBits64 hs word)
        else
          MkPartial word (index + 8) len' hs

--------------------------------------------------------------------------------
-- Incremental word processing
--------------------------------------------------------------------------------

||| Add a 16-bit word in little-endian byte order.
|||
||| Correctly handles any existing pending bytes.
export
%inline
addBits16 : PartialHash -> Bits16 -> PartialHash
addBits16 ph x =
  let ph = addBits8 ph (cast x)
   in addBits8 ph (cast (x `shr16` 8))

||| Add a 32-bit word in little-endian byte order.
|||
||| Correctly handles any existing pending bytes.
export
%inline
addBits32 : PartialHash -> Bits32 -> PartialHash
addBits32 ph x =
  let ph = addBits16 ph (cast x)
   in addBits16 ph (cast (x `shr32` 16))

||| Add a 64-bit word in little-endian byte order.
|||
||| Correctly handles any existing pending bytes.
|||
||| Unlike the original implementation, this function does not
||| bypass the partial message state.
export
%inline
addBits64 : PartialHash -> Bits64 -> PartialHash
addBits64 ph x =
  let ph = addBits32 ph (cast x)
   in addBits32 ph (cast (x `shr` 32))

--------------------------------------------------------------------------------
-- Finalization
--------------------------------------------------------------------------------

||| Finalize an incremental SipHash-2-4 computation.
|||
||| The final message word contains the remaining bytes and
||| the message length modulo 256 in its most significant byte.
|||
||| Finalization performs two compression rounds, followed by
||| four finalization rounds.
export
%inline
finish : PartialHash -> Bits64
finish (MkPartial tail index len hs) =
  let rest : Bits64
      rest = ((len `and64` 0xff) `shl` 56) `bor` tail
      st1  : HashState
      st1  = hashBits64 hs rest
      st2  : HashState
      st2  = { v2 $= (`xor` 0xff) } st1
      st3  : HashState
      st3  = repeat DROUNDS compress st2
   in (st3.v0 `xor` st3.v1) `xor` (st3.v2 `xor` st3.v3)

--------------------------------------------------------------------------------
-- Aligned word processing
--------------------------------------------------------------------------------

||| Add a complete 64-bit message word.
|||
||| When there are no pending bytes, compress the word directly.
||| Otherwise, fall back to the general incremental implementation.
|||
||| The fallback preserves correctness if this helper is ever
||| called with a non-aligned PartialHash.
%inline
addAlignedWord : PartialHash -> Bits64 -> PartialHash
addAlignedWord ph word =
  case ph of
    MkPartial tail index len hs =>
      if index == 0
        then MkPartial 0 0 (len + 8) (hashBits64 hs word)
        else addBits64 ph word

--------------------------------------------------------------------------------
-- Pending byte processing
--------------------------------------------------------------------------------

||| Complete an existing partial message block.
|||
||| Processes at most seven bytes.
|||
||| Stops when:
|||
||| - The pending block becomes complete.
||| - The input buffer is exhausted.
||| - The bounded number of iterations is exhausted.
|||
||| Returns the next buffer offset and number of bytes remaining.
|||
||| The caller must supply a valid buffer range.
fillPending :
     Ref World PartialHash
  -> Buffer
  -> (fuel : Nat)
  -> (offset : Nat)
  -> (remaining : Nat)
  -> F1 World (Nat, Nat)
fillPending r buf Z        offset remaining     t =
  (offset, remaining) # t
fillPending r buf (S fuel) offset Z             t =
  (offset, 0) # t
fillPending r buf (S fuel) offset (S remaining) t =
  let ph # t := read1 r t
   in if ph.index == 0
        then
          (offset, S remaining) # t
        else
          let byte # t := ioToF1 (getBits8 buf (cast offset)) t
              _    # t := mod1 r (\p => addBits8 p byte) t
           in fillPending
                r
                buf
                fuel
                (S offset)
                remaining
                t

--------------------------------------------------------------------------------
-- Complete 64-bit message blocks
--------------------------------------------------------------------------------

||| Process complete eight-byte message blocks.
|||
||| Each block is read as a little-endian Bits64 and compressed
||| directly into the incremental SipHash state.
|||
||| The caller guarantees that enough bytes remain and that the
||| partial state is aligned before entering this function.
|||
||| Returns the next unread buffer offset.
hashFullWords :
     Ref World PartialHash
  -> Buffer
  -> (count : Nat)
  -> (offset : Nat)
  -> F1 World Nat
hashFullWords r buf Z         offset t =
  offset # t
hashFullWords r buf (S count) offset t =
  let word # t := ioToF1 (getBits64 buf (cast offset)) t
      _    # t := mod1 r (\ph => addAlignedWord ph word) t
   in hashFullWords
        r
        buf
        count
        (offset + 8)
        t

--------------------------------------------------------------------------------
-- Trailing byte processing
--------------------------------------------------------------------------------

||| Process the remaining bytes after all complete message blocks.
|||
||| There are at most seven trailing bytes.
|||
||| Each byte is incorporated into the partial SipHash state.
|||
||| The caller guarantees that the requested range is valid.
hashTrailing :
     Ref World PartialHash
  -> Buffer
  -> (remaining : Nat)
  -> (offset : Nat)
  -> F1' World
hashTrailing r buf Z             offset t =
  () # t
hashTrailing r buf (S remaining) offset t =
  let byte # t := ioToF1 (getBits8 buf (cast offset)) t
      _    # t := mod1 r (\ph => addBits8 ph byte) t
   in hashTrailing
        r
        buf
        remaining
        (S offset)
        t

--------------------------------------------------------------------------------
-- Buffer hashing
--------------------------------------------------------------------------------

||| Add the complete contents of a buffer to an incremental
||| SipHash-2-4 computation.
|||
||| Processing occurs in three phases:
|||
||| 1. Complete any existing partial message block.
||| 2. Compress complete 64-bit message words directly.
||| 3. Accumulate the remaining zero to seven bytes.
|||
||| The buffer is never resized or modified.
|||
||| Multiple calls can be chained to hash a continuous byte stream.
export
hashBuffer : PartialHash -> Buffer -> IO PartialHash
hashBuffer ph buf = do
  rawLen <- rawSize buf
  if rawLen <= 0
    then pure ph
    else
      runIO $ \t =>
        let r # t := ref1 ph t
            remaining                 : Nat
            remaining                 := cast rawLen
            (offset1, remaining1) # t := fillPending r buf 7 0 remaining t
            fullWords                 : Nat
            fullWords                 := remaining1 `div` 8
            trailing                  : Nat
            trailing                  := remaining1 `mod` 8
            offset2               # t := hashFullWords r buf fullWords offset1 t
            _                     # t := hashTrailing r buf trailing offset2 t
         in read1 r t

--------------------------------------------------------------------------------
-- Convenience functions
--------------------------------------------------------------------------------

||| Hash a list of bytes using the fixed zero key.
|||
||| This function is pure and supports arbitrary byte sequences.
export
hashBytes : List Bits8 -> Bits64
hashBytes xs =
  finish (foldl addBits8 initPartial xs)

||| Hash a complete buffer using the fixed zero key.
|||
||| Unlike hashBuffer, this function returns the finalized hash.
export
hashBufferFinal : Buffer -> IO Bits64
hashBufferFinal buf = do
  ph <- hashBuffer initPartial buf
  pure (finish ph)
