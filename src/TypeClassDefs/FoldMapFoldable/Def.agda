{-# OPTIONS --prop #-}

module TypeClassDefs.FoldMapFoldable.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Monoid

record FoldMapFoldable {i} (T : Set i → Set i) : Set (lsuc i) where
  field
    foldMap : {M : Set i} → (monoid : Monoid M) → {A : Set i} → (A → M) → (T A → M)

  field
    FoldMap-MonoidHomomorphism :
      {M₁ M₂ : Set i} → {monoid₁ : Monoid M₁} → {monoid₂ : Monoid M₂} →
      (ψ : M₁ → M₂) → MonoidHomomorphism monoid₁ monoid₂ ψ →
      {A : Set i} → (f : A → M₁) → (α : T A) →
      foldMap monoid₂ (ψ ∘ f) α ＝ ψ (foldMap monoid₁ f α)

open FoldMapFoldable public
