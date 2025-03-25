{-# OPTIONS --prop #-}

module TypeClassDefs.FunctorWithUnit.Def where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.Functor

record FunctorWithUnit {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    FunctorOfWithUnit : Functor F
    unit : {A : Set i} → A → F A

  ufmap : {A B : Set i} → (A → B) → F A → F B
  ufmap = fmap FunctorOfWithUnit

  field
    Unit-Homomorphism : {A B : Set i} → (a : A) → (f : A → B) → ufmap f (unit a) ＝ unit (f a)

open FunctorWithUnit public
