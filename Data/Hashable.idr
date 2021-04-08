module Data.Hashable

||| A default salt used in the implementation of 'hash'.
defaultSalt : Bits64
defaultSalt = 14695981039346656037

||| Interface for type that can be hashed.
-- Minimal implementation: 'hashWithSalt'
public export
interface Hashable a where
    hashWithSalt : Bits64 -> a -> Bits64
    hash : a -> Bits64
    hash = hashWithSalt defaultSalt

||| Default implementation of 'hashWithSalt' for types which are smaller than Bits64 (eg Bits32, Int).
export
defaultHashWithSalt : Hashable a => Bits64 -> a -> Bits64
defaultHashWithSalt salt x = salt `combine` hash x
  where
    combine : Bits64 -> Bits64 -> Bits64
    combine h1 h2 = (h1 * 16777619) `prim__xor_Bits64` h2

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

