{-# LANGUAGE ScopedTypeVariables #-}
module GenRec.Total where

import GHC.Exts (inline)
import GenRec.Class (MonadRec, RecProg')

import GenRec.Class

newtype Total i o a = Total{unTotal :: (i -> o) -> a}

runTotal :: forall i o . RecProg' (Total i o) i o -> i -> o
runTotal prog = \ x -> go x
  where
    go :: i -> o
    go x = unTotal (prog x) go

{-# INLINE runTotal #-}

runTotalInline :: forall i o . RecProg' (Total i o) i o -> i -> o
runTotalInline prog = \ x -> go x
  where
    go :: i -> o
    go x = unTotal (inline prog x) go

{-# INLINE runTotalInline #-}

pureTotal :: a -> Total i o a
pureTotal x = Total (\ _ -> x)

bindTotal :: Total i o a -> (a -> Total i o b) -> Total i o b
bindTotal m k = Total (\ self -> unTotal (k (unTotal m self)) self)

instance Functor (Total i o) where
    fmap f m = bindTotal m (pureTotal . f)

instance Applicative (Total i o) where
    pure = pureTotal
    mf <*> m = bindTotal mf (<$> m)

instance Monad (Total i o) where
    (>>=) = bindTotal

instance MonadRec i o (Total i o) where
    recurse x = Total (\ self -> self x)

