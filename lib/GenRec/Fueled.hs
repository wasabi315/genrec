{-# LANGUAGE ScopedTypeVariables #-}
module GenRec.Fueled where

import GHC.Exts (inline)
import GenRec.Class (MonadRec, RecProg')
import Numeric.Natural (Natural)

import GenRec.Class

data Fuel = Zero
          | Suc Fuel
              deriving (Eq, Ord, Show)

natToFuel :: Natural -> Fuel
natToFuel n
  = if n == 0 then Zero else
      case pred n of
          n -> Suc (natToFuel n)

newtype Fueled i o a = Fueled{unFueled ::
                              (Fuel -> i -> Maybe o) -> Fuel -> Maybe a}

runFueled ::
          forall i o . RecProg' (Fueled i o) i o -> Fuel -> i -> Maybe o
runFueled f = go
  where
    go :: Fuel -> i -> Maybe o
    go n x = unFueled (f x) go n

{-# INLINE runFueled #-}

runFueledInline ::
                forall i o . RecProg' (Fueled i o) i o -> Fuel -> i -> Maybe o
runFueledInline f = go
  where
    go :: Fuel -> i -> Maybe o
    go n x = unFueled (inline f x) go n

{-# INLINE runFueledInline #-}

pureFueled :: a -> Fueled i o a
pureFueled x = Fueled (\ _ _ -> Just x)

bindFueled :: Fueled i o a -> (a -> Fueled i o b) -> Fueled i o b
bindFueled m k
  = Fueled
      (\ self n ->
         do x <- unFueled m self n
            unFueled (k x) self n)

instance Functor (Fueled i o) where
    fmap = \ m f -> bindFueled f (pureFueled . m)

instance Applicative (Fueled i o) where
    pure = pureFueled
    (<*>) = \ m mf -> bindFueled m (<$> mf)

instance Monad (Fueled i o) where
    (>>=) = bindFueled

instance MonadRec i o (Fueled i o) where
    recurse x
      = Fueled
          (\ self n ->
             case n of
                 Zero -> Nothing
                 Suc n -> self n x)

