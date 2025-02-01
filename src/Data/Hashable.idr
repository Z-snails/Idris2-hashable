module Data.Hashable

import Data.Vect

||| A default salt used in the implementation of 'hash'.
export
defaultSalt : Bits64
defaultSalt = 14695981039346656037

export infixl 10 `hashWithSalt`
export infixl 10 `hash`

||| Interface for type that can be hashed.
||| Minimal implementation: 'hashWithSalt'
public export
interface Hashable a where
    ||| Hash a value with the given salt
    total
    hashWithSalt : Bits64 -> a -> Bits64
    ||| Hash a value with the default salt
    total
    hash : a -> Bits64
    hash = hashWithSalt defaultSalt

||| Combine 2 hashes.
export
combine : Bits64 -> Bits64 -> Bits64
combine h1 h2 = (h1 * 16777619) `prim__xor_Bits64` h2

||| Default implementation of 'hashWithSalt' for types which are smaller than Bits64 (eg Bits32, Int).
export
defaultHashWithSalt : (a -> Bits64) -> Bits64 -> a -> Bits64
defaultHashWithSalt hash salt x = salt `combine` hash x

export
Hashable Bits8 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Bits16 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Bits32 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Bits64 where
    hash = id
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Int where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Int8 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Int16 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Int32 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Int64 where
    hash = cast
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Char where
    hash = cast . ord
    hashWithSalt = defaultHashWithSalt hash

export
Hashable Integer where
    hashWithSalt salt x = hashPositive (makeSalt salt x) (abs x)
      where
        makeSalt : Bits64 -> Integer -> Bits64
        makeSalt x y = if y >= 0
            then x
            else negate x

        bits64Max : Integer
        bits64Max = 1 `prim__shl_Integer` 64 - 1

        hashPositive : Bits64 -> Integer -> Bits64
        hashPositive salt x = if x > bits64Max
            then hashPositive
                (hashWithSalt salt
                    (cast {to=Bits64} (x `prim__and_Integer` bits64Max)))
                (assert_smaller x $ x `prim__shr_Integer` 64)
            else hashWithSalt salt (cast {to=Bits64} x)

export
Hashable Nat where
    hash x = hash (cast {to=Integer} x)
    hashWithSalt salt x = hashWithSalt salt (cast {to=Integer} x)

export
Hashable String where
    hashWithSalt salt str = finalise (foldl step (salt, 0) $ fastUnpack str)
      where
        step : (Bits64, Bits64) -> Char -> (Bits64, Bits64)
        step (s, l) x = (hashWithSalt s x, l + 1)
        finalise : (Bits64, Bits64) -> Bits64
        finalise (s, l) = hashWithSalt s l

export
Hashable Bool where
    hash False = 0
    hash True = 1
    
    hashWithSalt = defaultHashWithSalt hash

export
(Hashable a, Hashable b) => Hashable (a, b) where
    hashWithSalt salt (a, b) = salt `hashWithSalt` a `hashWithSalt` b

export
Hashable a => Hashable (Maybe a) where
    hashWithSalt salt Nothing = hashWithSalt salt 0
    hashWithSalt salt (Just x) = hashWithSalt salt 1 `hashWithSalt` x

export
Hashable a => Hashable (List a) where
    hashWithSalt salt [] = hashWithSalt salt 0
    hashWithSalt salt (x :: xs) =
        salt
            `hashWithSalt` 1
            `hashWithSalt` x
            `hashWithSalt` xs

export
Hashable a => Hashable (SnocList a) where
    hashWithSalt salt [<] = hashWithSalt salt 0
    hashWithSalt salt (sx :< x) =
        salt
            `hashWithSalt` 1
            `hashWithSalt` x
            `hashWithSalt` sx

export
Hashable a => Hashable (Vect len a) where
    hashWithSalt salt [] = hashWithSalt salt 0
    hashWithSalt salt (x :: xs) =
        salt
            `hashWithSalt` 1
            `hashWithSalt` x
            `hashWithSalt` xs

