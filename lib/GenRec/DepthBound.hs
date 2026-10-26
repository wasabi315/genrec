{-# LANGUAGE ScopedTypeVariables #-}
module GenRec.DepthBound
  (Depth(..), natToDepth, DepthBound(..), runDepthBound, runDepthBoundInline)
where

import GHC.Exts (inline)
import GenRec.Class (RecProg', Recurse(recurse))
import Numeric.Natural (Natural)

data Depth = Zero
           | Suc Depth
               deriving (Eq, Ord, Show)

natToDepth :: Natural -> Depth
natToDepth n
  = if n == 0 then Zero else
      case pred n of
          n -> Suc (natToDepth n)

newtype DepthBound i o a = DepthBound{unDepthBound ::
                                      (Depth -> i -> Maybe o) -> Depth -> Maybe a}

runDepthBound ::
              forall i o . RecProg' (DepthBound i o) i o -> Depth -> i -> Maybe o
runDepthBound f = go
  where
    go :: Depth -> i -> Maybe o
    go n x = unDepthBound (f x) go n

{-# INLINE runDepthBound #-}

runDepthBoundInline ::
                    forall i o . RecProg' (DepthBound i o) i o -> Depth -> i -> Maybe o
runDepthBoundInline f = go
  where
    go :: Depth -> i -> Maybe o
    go n x = unDepthBound (inline f x) go n

{-# INLINE runDepthBoundInline #-}

pureDB :: a -> DepthBound i o a
pureDB x = DepthBound (\ _ _ -> Just x)

bindDB ::
       DepthBound i o a -> (a -> DepthBound i o b) -> DepthBound i o b
bindDB m k
  = DepthBound
      (\ self n ->
         do x <- unDepthBound m self n
            unDepthBound (k x) self n)

instance Functor (DepthBound i o) where
    fmap = \ f m -> bindDB m (pureDB . f)

instance Applicative (DepthBound i o) where
    pure = pureDB
    (<*>) = \ mf m -> bindDB mf (<$> m)

instance Monad (DepthBound i o) where
    (>>=) = bindDB

instance Recurse i o (DepthBound i o) where
    recurse x
      = DepthBound
          (\ self n ->
             case n of
                 Zero -> Nothing
                 Suc n -> self n x)

