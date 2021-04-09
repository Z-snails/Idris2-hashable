module Data.Hashable

import Data.String

||| A default salt used in the implementation of 'hash'.
export
defaultSalt : Bits64
defaultSalt = 14695981039346656037

infixl 10 `hashWithSalt`
infixl 10 `hash`

||| Interface for type that can be hashed.
-- Minimal implementation: 'hashWithSalt'
public export
interface Hashable a where
    hashWithSalt : Bits64 -> a -> Bits64
    hash : a -> Bits64
    hash = hashWithSalt defaultSalt

||| Combine 2 hashes.
export
combine : Bits64 -> Bits64 -> Bits64
combine h1 h2 = (h1 * 16777619) `prim__xor_Bits64` h2

||| Default implementation of 'hashWithSalt' for types which are smaller than Bits64 (eg Bits32, Int).
export
defaultHashWithSalt : Hashable a => Bits64 -> a -> Bits64
defaultHashWithSalt salt x = salt `combine` hash x

export
Hashable Bits8 where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Bits16 where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Bits32 where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Bits64 where
    hash = id
    hashWithSalt = defaultHashWithSalt

export
Hashable Int where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Char where
    hash = cast . ord
    hashWithSalt = defaultHashWithSalt

export
Hashable String where
    hashWithSalt salt str = finalise (foldl step (salt, 0) $ fastUnpack str)
      where
        step : (Bits64, Bits64) -> Char -> (Bits64, Bits64)
        step (s, l) x = (hashWithSalt s x, l + 1)
        finalise : (Bits64, Bits64) -> Bits64
        finalise (s, l) = hashWithSalt s l
