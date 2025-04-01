{-# OPTIONS --prop #-}

module TypeClassDefs.Alternative.Def where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.Applicative

record Alternative {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    Alternative-to-Applicative : Applicative F
    empty : {A : Set i} → F A
    or : {A : Set i} → F A → F A → F A

  field
    Empty-Identity-Left : {A : Set i} → (α : F A) → or empty α ＝ α
    Empty-Identity-Right : {A : Set i} → (α : F A) → or α empty ＝ α
    Or-Associative : {A : Set i} → (α β γ : F A) → or (or α β) γ ＝ or α (or β γ)
