module Data.Hashable.Lifted

import Data.Hashable

||| A value used to distinguish between data constructors.
distinguisher : Bits64
distinguisher = 0x5555555555555555

infixl 10 `hashWithSalt1`

||| Interface for higher-kinded types that can be hashed, if the element they contain can be hashed.
interface Hashable1 t where
    hashWithSalt1 : (Bits64 -> a -> Bits64) -> Bits64 -> t a -> Bits64

export
Hashable a => Hashable1 t => Hashable (t a) where
    hashWithSalt = hashWithSalt1 hashWithSalt

export
Hashable1 Maybe where
    hashWithSalt1 hws s Nothing = 0
    hashWithSalt1 hws s (Just x) = s `hashWithSalt` distinguisher `hws` x

export
Hashable1 List where
    hashWithSalt1 hws s xs = finalise (foldl step (s, 0) xs)
      where
        step : (Bits64, Bits64) -> a -> (Bits64, Bits64)
        step (s, l) x = (hws s x, l + 1)
        finalise : (Bits64, Bits64) -> Bits64
        finalise (s, l) = hashWithSalt s l
