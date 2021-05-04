module Data.Hashable.Lifted

import Data.Vect

import Data.Hashable

infixl 10 `hashWithSalt1`

||| Interface for higher-kinded types that can be hashed, if the element they contain can be hashed.
interface Hashable1 t where
    hashWithSalt1 : (Bits64 -> a -> Bits64) -> Bits64 -> t a -> Bits64

export
Hashable a => Hashable1 t => Hashable (t a) where
    hashWithSalt = hashWithSalt1 hashWithSalt

||| Hashable implementation for any foldable.
export
[Hashable1Foldable] Foldable t => Hashable1 t where
    hashWithSalt1 hws s xs = finalise (foldl step (s, 0) xs)
      where
        step : (Bits64, Bits64) -> a -> (Bits64, Bits64)
        step (s, l) x = (hws s x, l + 1)
        finalise : (Bits64, Bits64) -> Bits64
        finalise (s, l) = hashWithSalt s l

export
Hashable1 Maybe where
    hashWithSalt1 hws s Nothing = s
    hashWithSalt1 hws s (Just x) = 1 `hashWithSalt` s `hws` x

export
Hashable1 List where
    hashWithSalt1 = hashWithSalt1 @{Hashable1Foldable}

export
Hashable1 (Vect len) where
    hashWithSalt1 = hashWithSalt1 @{Hashable1Foldable}
