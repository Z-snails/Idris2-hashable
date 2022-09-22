
||| SipHash24 copied from C [reference implementation](https://github.com/veorq/SipHash/blob/master/siphash.c)
module Data.Hashable.SipHash

import Data.Buffer
import Data.IORef

%default total

%inline
CROUNDS : Nat
CROUNDS = 2

%inline
DROUNDS : Nat
DROUNDS = 4

record State where
    constructor MkState
    v0 : Bits64
    v1 : Bits64
    v2 : Bits64
    v3 : Bits64

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
and : Int -> Int -> Int
and = prim__and_Int

%inline
%spec b
rotl : Bits64 -> (b : Bits64) -> Bits64
rotl x b = (x `shl` b) `bor` (x `shr` (64 - b))

||| Make the length the smallest multiple of 8 bytes >= the given number
%inline
fullSize : Int -> Int
fullSize x =
    let left = x `prim__and_Int` 7
     in if (x `prim__and_Int` 7) == 0
        then x
        else x - left + 8

-- %inline
compress : IORef State -> IO ()
compress stref = do
    MkState v0 v1 v2 v3 <- readIORef stref
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
    writeIORef stref $ MkState v0 v1 v2 v3

-- this could all be in ST, but Buffer doesn't support it
%inline
siphashInit : IO (IORef State)
siphashInit = newIORef $ MkState
    { v0 = 0x736f6d6570736575
    , v1 = 0x646f72616e646f6d
    , v2 = 0x6c7967656e657261
    , v3 = 0x7465646279746573
    }

%inline
%spec count
repeat : (count : Nat) -> IO () -> IO ()
repeat Z _ = pure ()
repeat (S k) act = act >> repeat k act

siphashLoop : IORef State -> Buffer -> Int -> Int -> IO ()
siphashLoop stref buf idx len = if idx >= len
    then pure ()
    else do
        m <- getBits64 buf idx
        repeat CROUNDS $ compress stref
        siphashLoop stref buf (assert_smaller idx $ idx + 8) len

%inline
siphashLeftover : IORef State -> Buffer -> Int -> Int -> Int -> IO Bits64
siphashLeftover stref buf size left idx = do
    x <- getBits64 buf idx
    pure $ x `bor` (cast size `shl` 56)

siphash : Buffer -> IO Bits64
siphash buf = do
    stref <- siphashInit
    size <- fullSize <$> rawSize buf
    siphashLoop stref buf 0 size
    let left = size `and` 7
    b <- siphashLeftover stref buf size (size - left) left
    modifyIORef stref $ { v3 $= (`xor` b) }
    repeat DROUNDS $ compress stref
    modifyIORef stref $ { v0 $= (`xor` b) }
    MkState v0 v1 v2 v3 <- readIORef stref
    pure $ (v0 `xor` v1) `xor` (v2 `xor` v3)

export
siphashString : String -> Bits64
siphashString str = unsafePerformIO $ do
    Just buf <- newBuffer $ fullSize $ stringByteLength str
        | Nothing => assert_total $ idris_crash "Error allocating buffer"
    setString buf 0 str
    siphash buf
