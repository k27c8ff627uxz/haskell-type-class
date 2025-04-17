{-# OPTIONS --prop #-}

module TypeClassDefs.FoldableWithFunctor.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Functor
open import TypeClassDefs.Monoid

record FoldableWithFunctor {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    FoldableWithFunctor-to-Functor : Functor F
    fold : {M : Set i} → (monoid : Monoid M) → F M → M

  fofmap : {A B : Set i} → (A → B) → (F A → F B)
  fofmap = fmap FoldableWithFunctor-to-Functor
  
  field
    Fold-FmapHomomorphism : {A₁ A₂ M : Set i} → (monoid : Monoid M) → (r : A₂ → M) → (f : A₁ → A₂) → (α : F A₁) → fold monoid (fofmap (r ∘ f) α) ＝ fold monoid (fofmap r (fofmap f α))
    Fold-MonoidHomomorphism : {M₁ M₂ : Set i} → (monoid₁ : Monoid M₁) → (monoid₂ : Monoid M₂) → (ψ : M₁ → M₂) → (MonoidHomomorphism monoid₁ monoid₂ ψ) → (α : F M₁) → fold monoid₂ (fofmap ψ α) ＝ ψ (fold monoid₁ α)

open FoldableWithFunctor public
