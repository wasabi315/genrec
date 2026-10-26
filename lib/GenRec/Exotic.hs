{-# LANGUAGE ScopedTypeVariables #-}
module GenRec.Exotic
  (FunList(..), sell, runFunList)
where

import GenRec.Class (RecProg', Recurse(recurse))

data FunList i o a = Done a
                   | More i (FunList i o (o -> a))

fmapFL :: (a -> b) -> FunList i o a -> FunList i o b
fmapFL f (Done x) = Done (f x)
fmapFL f (More x xs) = More x (fmapFL (f .) xs)

liftA2FL ::
         (a -> b -> c) -> FunList i o a -> FunList i o b -> FunList i o c
liftA2FL f (Done x) ys = fmapFL (f x) ys
liftA2FL f (More x xs) ys
  = More x (liftA2FL (\ g z w -> f (g w) z) xs ys)

sell :: i -> FunList i o o
sell x = More x (Done id)

instance Functor (FunList i o) where
    fmap = fmapFL

instance Applicative (FunList i o) where
    pure = Done
    (<*>) = liftA2FL id

instance Recurse i o (FunList i o) where
    recurse = sell

runFunList :: forall i o . RecProg' (FunList i o) i o -> i -> o
runFunList f = g
  where
    g :: i -> o
    g x = h (f x)
    h :: FunList i o a -> a
    h (Done x) = x
    h (More x m) = h m (g x)

