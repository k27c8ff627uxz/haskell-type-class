{-# OPTIONS --prop #-}

module TypeClassDefs.MonadPlus.Def where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.Monad

record MonadPlus {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    MonadPlus-to-Monad : Monad F
    mzero : {A : Set i} → F A
    mplus : {A : Set i} → F A → F A → F A

  mreturn : {A : Set i} → A → F A
  mreturn = return MonadPlus-to-Monad
  
  mpbind : {A B : Set i} → F A → (A → F B) → F B
  mpbind = bind MonadPlus-to-Monad

  field
    MZero-Identity-Left : {A : Set i} → (α : F A) → mplus mzero α ＝ α
    MZero-Identity-Right : {A : Set i} → (α : F A) → mplus α mzero ＝ α
    MPlus-Associative : {A : Set i} → (α β γ : F A) → mplus (mplus α β) γ ＝ mplus α (mplus β γ)
    MPBind-Left-Zero : {A B : Set i} → (f : A → F B) → mpbind mzero f ＝ mzero
    MPBind-Right-Zero : {A B : Set i} → (α : F A) → mpbind α (\_ → mzero {B}) ＝ mzero {B}

open MonadPlus public
