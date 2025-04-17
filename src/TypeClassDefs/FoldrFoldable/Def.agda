{-# OPTIONS --prop #-}

module TypeClassDefs.FoldrFoldable.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Monoid

record FoldrFoldable {i} (T : Set i → Set i) : Set (lsuc i) where
  field
    foldr : {A B : Set i} → (A → B → B) → B → T A → B

  field
    Foldr-MonoidHomomorphism :
      {M₁ M₂ : Set i} → {monoid₁ : Monoid M₁} → {monoid₂ : Monoid M₂} → (ψ : M₁ → M₂) → MonoidHomomorphism monoid₁ monoid₂ ψ →
      {A : Set i} → (f : A → M₁) → (α : T A) →
      foldr (\a → \b → mappend monoid₂ ((ψ ∘ f) a) b) (mempty monoid₂) α ＝ ψ (foldr (\a → \b → mappend monoid₁ (f a) b) (mempty monoid₁) α)
    Foldr-Destruct : {A B : Set i} → (f : A → B → B) → (α : T A) → (b : B) → foldr f b α ＝ foldr (\a → \(r : B → B) → (\b → f a (r b))) (id B) α b
open FoldrFoldable public
