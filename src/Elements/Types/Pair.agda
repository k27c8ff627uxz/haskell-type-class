{-# OPTIONS --prop #-}

module Elements.Types.Pair where

open import Agda.Primitive
open import Logic
open import Elements.Function

record Pair {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B

open Pair public

assoc-Pair : {i j k : Level} → {A : Set i} → {B : Set j} → {C : Set k} → Pair (Pair A B) C → Pair A (Pair B C)
assoc-Pair {i} {j} {k} {A} {B} {C} ((a , b) , c) = (a , (b , c))

curry : {i₁ i₂ i₃ : Level} → {A : Set i₁} → {B : Set i₂} → {C : Set i₃} → (Pair A B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : {i₁ i₂ i₃ : Level} → {A : Set i₁} → {B : Set i₂} → {C : Set i₃} → (A → B → C) → (Pair A B → C)
uncurry f (a , b) = f a b

createPair : {i j : Level} → {A : Set i} → {B : Set j} → A → B → Pair A B
createPair {i} {j} {A} {B} = curry (id (Pair A B))

pMapApply : {i : Level} → {A B : Set i} → Pair (A → B) A → B
pMapApply {i} {A} {B} = uncurry (id (A → B))
