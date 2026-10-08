{-# LANGUAGE ScopedTypeVariables #-}
module GenRec.Direct where

import GHC.Exts (inline)
import GenRec.Class (MonadRec, RecProg')

import GenRec.Class

newtype Direct i o a = Direct{unDirect :: (i -> o) -> a}

runDirect :: forall i o . RecProg' (Direct i o) i o -> i -> o
runDirect f = go
  where
    go :: i -> o
    go x = unDirect (f x) go

{-# INLINE runDirect #-}

runDirectInline :: forall i o . RecProg' (Direct i o) i o -> i -> o
runDirectInline f = go
  where
    go :: i -> o
    go x = unDirect (inline f x) go

{-# INLINE runDirectInline #-}

pureDirect :: a -> Direct i o a
pureDirect x = Direct (\ _ -> x)

bindDirect :: Direct i o a -> (a -> Direct i o b) -> Direct i o b
bindDirect m k
  = Direct (\ self -> unDirect (k (unDirect m self)) self)

instance Functor (Direct i o) where
    fmap = \ m f -> bindDirect f (pureDirect . m)

instance Applicative (Direct i o) where
    pure = pureDirect
    (<*>) = \ m mf -> bindDirect m (<$> mf)

instance Monad (Direct i o) where
    (>>=) = bindDirect

instance MonadRec i o (Direct i o) where
    recurse x = Direct (\ self -> self x)

