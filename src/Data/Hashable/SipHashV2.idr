
||| SipHash24 copied from C [reference implementation](https://github.com/veorq/SipHash/blob/master/siphash.c)
||| and rust https://doc.rust-lang.org/src/core/hash/sip.rs.html
module Data.Hashable.SipHashV2

import Data.Buffer

%default total

%inline
CROUNDS : Nat
CROUNDS = 2

%inline
DROUNDS : Nat
DROUNDS = 4

record HashState where
    constructor MkST
    v0 : Bits64
    v1 : Bits64
    v2 : Bits64
    v3 : Bits64

initHashState : HashState
initHashState = MkST
    { v0 = 0x736f6d6570736575
    , v1 = 0x646f72616e646f6d
    , v2 = 0x6c7967656e657261
    , v3 = 0x7465646279746573
    }

record PartialHash where
    constructor MkPartial
    tail : Bits64
    index : Bits64
    length : Bits64
    hst : HashState

initPartial : PartialHash
initPartial = MkPartial 0 0 0 initHashState

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
and : Bits64 -> Bits64 -> Bits64
and = prim__and_Bits64

%inline
shr16 : Bits16 -> Bits16 -> Bits16
shr16 = prim__shr_Bits16

%inline
shr32 : Bits32 -> Bits32 -> Bits32
shr32 = prim__shr_Bits32

%inline
andInt : Int -> Int -> Int
andInt = prim__and_Int

%inline
%spec b
rotl : Bits64 -> (b : Bits64) -> Bits64
rotl x b = (x `shl` b) `bor` (x `shr` (64 - b))

-- Make the length the smallest multiple of 8 tail >= the given number
%inline
fullSize : Int -> Int
fullSize x =
    let left = x `andInt` 7
     in if (x `andInt` 7) == 0
        then x
        else x - left + 8

compress : HashState -> HashState
compress (MkST v0 v1 v2 v3) =
    let v0 = v0 + v1;
        v1 = v1 `rotl` 13;
        v1 = v1 `xor` v0;
        v0 = v0 `rotl` 32;
        v2 = v2 + v3;
        v3 = v3 `rotl` 16;
        v3 = v3 `xor` v2;
        v0 = v0 + v3;
        v3 = v3 `rotl` 21;
        v3 = v3 `xor` v0;
        v2 = v2 + v1;
        v1 = v1 `rotl` 17;
        v1 = v1 `xor` v2;
        v2 = v2 `rotl` 32;
    in MkST v0 v1 v2 v3

%inline
%spec rounds, f
repeat : (rounds : Nat) -> (f : a -> a) -> a -> a
repeat Z f x = x
repeat (S k) f x = repeat k f (f x)

%inline
hashBits64 : HashState -> Bits64 -> HashState
hashBits64 (MkST v0 v1 v2 v3) m =
    let v3 = v3 `xor` m
        MkST v0 v1 v2 v3 = repeat CROUNDS compress $ MkST v0 v1 v2 v3
        v0 = v0 `xor` m
     in MkST v0 v1 v2 v3

export
finish : PartialHash -> Bits64
finish (MkPartial tail index length hst) =
    let MkST v0 v1 v2 v3 = hst
        rest = ((length `and` 0xff) `shl` 56) `bor` tail
        v3 = v3 `xor` rest
        MkST v0 v1 v2 v3 = repeat CROUNDS compress $ MkST v0 v1 v2 v3
        v0 = v0 `xor` rest
        v2 = v2 `xor` 0xff
        MkST v0 v1 v2 v3 = repeat DROUNDS compress $ MkST v0 v1 v2 v3
     in (v0 `xor` v1) `xor` (v2 `xor` v3)

export
addBits8 : PartialHash -> Bits8 -> PartialHash
addBits8 (MkPartial tail index len hs) x = case index of
    -- finished a set of tail
    56 => MkPartial 0 0 (len + 1) $ hashBits64 hs (tail `bor` (cast x `shl` 56))
    -- add byte to partial
    _ => MkPartial (tail `bor` (cast x `shl` index)) (index + 8) (len + 1) hs

export
addBits16 : PartialHash -> Bits16 -> PartialHash
addBits16 ph x = addBits8 (addBits8 ph $ cast x) (cast $ x `shr16` 8)

export
addBits32 : PartialHash -> Bits32 -> PartialHash
addBits32 ph x = addBits16 (addBits16 ph $ cast x) (cast $ x `shr32` 16)

export
addBits64 : PartialHash -> Bits64 -> PartialHash
addBits64 (MkPartial tail index length hst) x = MkPartial tail index (length + 8) $ hashBits64 hst x

hashBuffer' : PartialHash -> Buffer -> Int -> Int -> IO PartialHash
hashBuffer' ph buf len idx = if idx >= len
    then pure ph
    else do
        word <- getBits64 buf idx
        let ph = addBits64 ph word
        hashBuffer' ph buf len (assert_smaller idx $ idx + 8)

hashBuffer : PartialHash -> Buffer -> IO PartialHash
hashBuffer ph buf = do
    rawLen <- rawSize buf
    let len = fullSize rawLen
    Just buf' <- resizeBuffer buf len
        | Nothing => hashBuffer' ph buf (rawLen `andInt` (- 7)) 0
    hashBuffer' ph buf' len 0
