{-# OPTIONS --prop #-}

module TypeClassDefs.CategoricalMonad.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.FunctorWithUnit

record CategoricalMonad {i : Level} (F : Set i → Set i) : Set (lsuc i) where
  field
    CategoricalMonad-to-FunctorWithUnit : FunctorWithUnit F
    unions : {A : Set i} → F (F A) → F A

  cunit : {A : Set i} → A → F A
  cunit = unit CategoricalMonad-to-FunctorWithUnit

  cmfmap : {A B : Set i} → (A → B) → F A → F B
  cmfmap = ufmap CategoricalMonad-to-FunctorWithUnit

  field
    unions-natural : {A B : Set i} → (f : A → B) → unions ∘ (cmfmap (cmfmap f)) ＝ (cmfmap f) ∘ unions
    cm-laxbicategory-comp : {A : Set i} → unions ∘ unions ＝ unions ∘ (cmfmap {F (F A)} unions)
    cm-laxbicategory-id-F : {A : Set i} → unions ∘ (cmfmap cunit) ＝ id (F A)
    cm-laxbicategory-id : {A : Set i} → unions ∘ cunit ＝ id (F A)

open CategoricalMonad public
