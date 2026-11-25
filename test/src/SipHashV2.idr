||| Incremental and buffer SipHash-2-4 regression tests.
module SipHashV2

import Data.Buffer
import Data.Hashable.SipHashV2
import Data.List
import Hedgehog

%default total

||| Reconstruct the little-endian bytes represented by a word.
bytes16 : Bits16 -> List Bits8
bytes16 x =
  [ cast x
  , cast (prim__shr_Bits16 x 8)
  ]

bytes32 : Bits32 -> List Bits8
bytes32 x =
  [ cast x
  , cast (prim__shr_Bits32 x 8)
  , cast (prim__shr_Bits32 x 16)
  , cast (prim__shr_Bits32 x 24)
  ]

bytes64 : Bits64 -> List Bits8
bytes64 x =
  [ cast x
  , cast (prim__shr_Bits64 x 8)
  , cast (prim__shr_Bits64 x 16)
  , cast (prim__shr_Bits64 x 24)
  , cast (prim__shr_Bits64 x 32)
  , cast (prim__shr_Bits64 x 40)
  , cast (prim__shr_Bits64 x 48)
  , cast (prim__shr_Bits64 x 56)
  ]

||| Check that incremental processing is independent of chunk boundaries.
propChunking : Property
propChunking = property $ do
  xs <- forAll $ list (linear 0 128) anyBits8
  ys <- forAll $ list (linear 0 128) anyBits8
  let first = foldl addBits8 initPartial xs
      result = foldl addBits8 first ys
  finish result === hashBytes (xs ++ ys)

||| A 16-bit update must respect any already pending bytes.
propBits16 : Property
propBits16 = property $ do
  initialBytes <- forAll $ list (linear 0 15) anyBits8
  word <- forAll anyBits16
  let ph = foldl addBits8 initPartial initialBytes
  finish (addBits16 ph word) ===
    hashBytes (initialBytes ++ bytes16 word)

||| A 32-bit update must respect any already pending bytes.
propBits32 : Property
propBits32 = property $ do
  initialBytes <- forAll $ list (linear 0 15) anyBits8
  word <- forAll anyBits32
  let ph = foldl addBits8 initPartial initialBytes
  finish (addBits32 ph word) ===
    hashBytes (initialBytes ++ bytes32 word)

||| Regression for the original addBits64 bug with pending bytes.
propBits64 : Property
propBits64 = property $ do
  initialBytes <- forAll $ list (linear 0 15) anyBits8
  word <- forAll anyBits64
  let ph = foldl addBits8 initPartial initialBytes
  finish (addBits64 ph word) ===
    hashBytes (initialBytes ++ bytes64 word)

||| Checks the exact byte boundary that was broken by addBits64.
propBits64Pending : Property
propBits64Pending = property $ do
  let ph = addBits8 initPartial 0xaa
      word : Bits64
      word = 0x0807060504030201
  finish (addBits64 ph word) ===
    hashBytes [0xaa, 1, 2, 3, 4, 5, 6, 7, 8]

||| Mix multiple word sizes across misaligned boundaries.
propMixedWidths : Property
propMixedWidths = property $ do
  a <- forAll anyBits8
  b <- forAll anyBits16
  c <- forAll anyBits32
  d <- forAll anyBits64
  let ph0 = addBits8 initPartial a
      ph1 = addBits16 ph0 b
      ph2 = addBits32 ph1 c
      ph3 = addBits64 ph2 d
      bytes = [a] ++ bytes16 b ++ bytes32 c ++ bytes64 d
  finish ph3 === hashBytes bytes

||| The incremental implementation must match independent reference values.
vector : List Bits8 -> Bits64 -> Property
vector bytes expected = property $ do
  hashBytes bytes === expected

export
suite : Group
suite = MkGroup "SipHashV2"
  [ ("empty input", vector [] 0x1e924b9d737700d7)
  , ("one byte", vector [0x61] 0x96c20860cd93a249)
  , ("three bytes", vector [0x61,0x62,0x63] 0x3fc884964770eede)
  , ("eight bytes", vector
        [0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68]
        0xe65ba172cce22193)
  , ("nine bytes", vector
        [0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]
        0x53273c4a18d0258c)
  , ("chunking equivalence", propChunking)
  , ("addBits16 equivalence", propBits16)
  , ("addBits32 equivalence", propBits32)
  , ("addBits64 equivalence", propBits64)
  , ("addBits64 pending-byte regression", propBits64Pending)
  , ("mixed-width equivalence", propMixedWidths)
  ]

||| Fill a Buffer with a list of bytes, in logical order.
fill : Buffer -> Nat -> List Bits8 -> IO ()
fill buf offset [] = pure ()
fill buf offset (x :: xs) = do
  setBits8 buf (cast offset) x
  fill buf (S offset) xs

||| Ensure buffer hashing and list hashing agree (without zero padding).
checkBuffer : List Bits8 -> IO Bool
checkBuffer xs = do
  Just buf <- newBuffer (cast (length xs))
    | Nothing => pure False
  fill buf 0 xs
  actual <- hashBufferFinal buf
  pure (actual == hashBytes xs)

||| Check hashing two buffers as a continuous stream, including any
||| partially filled 64-bit word at the buffer boundary.
checkTwoBuffers : List Bits8 -> List Bits8 -> IO Bool
checkTwoBuffers xs ys = do
  Just left <- newBuffer (cast (length xs))
    | Nothing => pure False
  Just right <- newBuffer (cast (length ys))
    | Nothing => pure False
  fill left 0 xs
  fill right 0 ys
  p1 <- hashBuffer initPartial left
  p2 <- hashBuffer p1 right
  pure (finish p2 == hashBytes (xs ++ ys))

||| Generate a deterministic test message of the requested length.
sequenceBytes : Nat -> List Bits8
sequenceBytes Z = []
sequenceBytes (S k) = sequenceBytes k ++ [cast k]

||| Exercise every nonempty length around several eight-byte boundaries.
checkLengths : Nat -> IO Bool
checkLengths Z = pure True
checkLengths (S k) = do
  current <- checkBuffer (sequenceBytes (S k))
  previous <- checkLengths k
  pure (current && previous)

--------------------------------------------------------------------------------
-- Optimized buffer tests
--------------------------------------------------------------------------------

||| Write a list of bytes into a buffer.
writeBytes : Buffer -> Int -> List Bits8 -> IO ()
writeBytes buf offset [] =
  pure ()

writeBytes buf offset (x :: xs) = do
  setBits8 buf offset x
  writeBytes buf (offset + 1) xs

||| Verify that optimized buffer hashing agrees with the pure
||| incremental implementation for an arbitrary initial state.
checkOptimizedBuffer :
     List Bits8
  -> List Bits8
  -> IO Bool
checkOptimizedBuffer initialBytes chunk = do
  Just buf <- newBuffer (cast (length chunk))
    | Nothing => pure False
  writeBytes buf 0 chunk
  let initial =
        foldl addBits8 initPartial initialBytes
  actual <- hashBuffer initial buf
  let expected =
        foldl addBits8 initial chunk
  pure (finish actual == finish expected)

||| Verify the optimized buffer implementation across all possible
||| pending-byte counts and important eight-byte boundaries.
testOptimizedBoundaries : IO Bool
testOptimizedBoundaries = do
  let input : List Bits8
      input = sequenceBytes 128
  let pendingSizes : List Nat
      pendingSizes = [0, 1, 2, 3, 4, 5, 6, 7]
  let bufferSizes : List Nat
      bufferSizes =
        [ 0, 1, 2, 3, 4, 5, 6, 7
        , 8, 9, 10, 14, 15, 16, 17
        , 23, 24, 25, 31, 32, 33
        , 63, 64, 65, 127
        ]
  results <- traverse
    (\pendingSize =>
      traverse
        (\bufferSize =>
          checkOptimizedBuffer
            (take pendingSize input)
            (take bufferSize input))
        bufferSizes)
    pendingSizes
  pure (all (all id) results)

export
bufferTests : IO Bool
bufferTests = do
  lengths             <- checkLengths 33
  split1              <- checkTwoBuffers [0xaa] [1,2,3,4,5,6,7,8]
  split7              <- checkTwoBuffers [0,1,2,3,4,5,6] [7,8,9,10]
  split8              <- checkTwoBuffers [0,1,2,3,4,5,6,7] [8,9,10]
  split9              <- checkTwoBuffers [0,1,2,3,4,5,6,7,8] [9,10,11]
  optimizedbuffer     <- checkOptimizedBuffer [0xaa, 0xbb, 0xcc] (sequenceBytes 33)
  optimizedboundaries <- testOptimizedBoundaries
  pure ( lengths         &&
         split1          &&
         split7          &&
         split8          &&
         split9          &&
         optimizedbuffer &&
         optimizedboundaries
       )
