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
  FOFmap-Identity : {A : Set i} →  fofmap (id A) ＝ id (F A)
  FOFmap-Identity = Fmap-Identity FoldableWithFunctor-to-Functor
  FOFmap-Composition : {A B C : Set i} → {f : B → C} → {g : A → B} → fofmap (f ∘ g) ＝ (fofmap f) ∘ (fofmap g)
  FOFmap-Composition = Fmap-Composition FoldableWithFunctor-to-Functor

  field
    Fold-MonoidHomomorphism : {M₁ M₂ : Set i} → (monoid₁ : Monoid M₁) → (monoid₂ : Monoid M₂) → (ψ : M₁ → M₂) → (MonoidHomomorphism monoid₁ monoid₂ ψ) → (α : F M₁) → fold monoid₂ (fofmap ψ α) ＝ ψ (fold monoid₁ α)

open FoldableWithFunctor public
