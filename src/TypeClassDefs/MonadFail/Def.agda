{-# OPTIONS --prop #-}

module TypeClassDefs.MonadFail.Def where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.Monad

record MonadFail {i} (E : Set i) (F : Set i → Set i) : Set (lsuc i) where
  field
    MonadFail-to-Monad : Monad F
    fail : {A : Set i} → E → F A

  mfbind : {A B : Set i} → F A → (A → F B) → F B
  mfbind = bind MonadFail-to-Monad
  
  field
    Fail-Law : {A B : Set i} → (e : E) → (f : A → F B) → mfbind (fail e) f ＝ fail e

open MonadFail public
