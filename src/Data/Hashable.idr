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

||| Default implementation of 'hashWithSalt' given a salt-less hashing function for types which are
||| smaller than Bits64 (eg Bits32, Int).
|||
||| @ hash A function to hash the value without a specified salt, such as `hash` on `Hashable`.
export
defaultHashWithSalt : (hash : a -> Bits64) -> Bits64 -> a -> Bits64
defaultHashWithSalt hash salt x = salt `combine` hash x

export total
Hashable Bits8 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export total
Hashable Bits16 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export total
Hashable Bits32 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export total
Hashable Bits64 where
    hash = id
    hashWithSalt = defaultHashWithSalt hash

export total
Hashable Int where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export total
Hashable Char where
    hash = cast . ord
    hashWithSalt = defaultHashWithSalt hash

export
Hashable String where
    hashWithSalt salt str = finalise (foldl step (salt, 0) $ fastUnpack str)
      where
        step : (Bits64, Bits64) -> Char -> (Bits64, Bits64)
        step (s, l) x = (hashWithSalt s x, l + 1)
        finalise : (Bits64, Bits64) -> Bits64
        finalise (s, l) = hashWithSalt s l
