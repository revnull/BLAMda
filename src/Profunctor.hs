
module Profunctor(Profunctor(..)) where

class Profunctor f where
    dimap :: (a -> b) -> (c -> d) -> f b c -> f a d
    dimap f g = lmap f . rmap g
    lmap :: (a -> b) -> f b c -> f a c
    lmap f = dimap f id
    rmap :: (a -> b) -> f c a -> f c b
    rmap f = dimap id f

instance Profunctor (->) where
    dimap ab cd bc = cd . bc . ab
    lmap = flip (.)
    rmap = (.)

