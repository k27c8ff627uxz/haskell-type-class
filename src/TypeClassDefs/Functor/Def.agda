{-# OPTIONS --prop #-}

module TypeClassDefs.Functor.Def where

open import Agda.Primitive
open import Logic
open import Elements

record Functor {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    fmap : ∀{A B} → (A → B) → F A → F B
    Fmap-Identity : {A : Set i} →  fmap (id A) ＝ id (F A)
    Fmap-Composition : {A B C : Set i} → {f : B → C} → {g : A → B} → fmap (f ∘ g) ＝ (fmap f) ∘ (fmap g)

open Functor public

fmap-const : {i : Level} → {F : Set i → Set i} → (functor : Functor F) → {A B : Set i} → A → F B → F A
fmap-const functor {A} {B} = (fmap functor) ∘ (const A B)
