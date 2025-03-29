{-# OPTIONS --prop #-}

module TypeClassDefs.FunctorWithUnit.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Functor

record FunctorWithUnit {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    FunctorWithUnit-to-Functor : Functor F
    unit : {A : Set i} → A → F A

  ufmap : {A B : Set i} → (A → B) → F A → F B
  ufmap = fmap FunctorWithUnit-to-Functor

  field
    Unit-Homomorphism : {A B : Set i} → (a : A) → (f : A → B) → ufmap f (unit a) ＝ unit (f a)

  UFmap-Identity : {A : Set i} →  ufmap (id A) ＝ id (F A)
  UFmap-Identity = Fmap-Identity FunctorWithUnit-to-Functor
  UFmap-Composition : {A B C : Set i} → {f : B → C} → {g : A → B} → ufmap (f ∘ g) ＝ (ufmap f) ∘ (ufmap g)
  UFmap-Composition = Fmap-Composition FunctorWithUnit-to-Functor

open FunctorWithUnit public
