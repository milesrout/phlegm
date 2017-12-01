{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

module Freer where

data Freer f a where
    Pure :: a -> Freer f a
    Free :: f x -> (x -> Freer f a) -> Freer f a

eta :: f a -> Freer f a
eta x = Free x Pure

instance Functor (Freer f) where
    fmap f (Pure x)   = Pure (f x)
    fmap f (Free u q) = Free u (fmap f . q)

instance Applicative (Freer f) where
    pure              = Pure
    Pure f   <*> x    = fmap f x
    Free u q <*> x    = Free u ((<*> x) . q)

instance Monad (Freer f) where
    return            = Pure
    Pure x   >>= k    = k x
    Free u l >>= k    = Free u (l >>> k)

(>>>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >>> g = (>>= g) . f
