{-# OPTIONS --sized-types #-}

module GenRec where

open import Haskell.Prelude
open import GenRec.Class  public
open import GenRec.Direct public
open import GenRec.Fueled public
open import GenRec.Free   public
open import GenRec.Total  public

--------------------------------------------------------------------------------

Keep : Type
Keep = Nat
{-# COMPILE AGDA2HS Keep #-}
