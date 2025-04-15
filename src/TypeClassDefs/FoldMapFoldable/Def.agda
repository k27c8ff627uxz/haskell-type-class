{-# OPTIONS --prop #-}

module TypeClassDefs.FoldMapFoldable.Def where

open import Agda.Primitive
open import TypeClassDefs.Monoid

record FoldMapFoldable {i} (T : Set i → Set i) : Set (lsuc i) where
  field
    foldMap : {M : Set i} → (monoid : Monoid M) → {A : Set i} → (A → M) → (T A → M)

open FoldMapFoldable public
