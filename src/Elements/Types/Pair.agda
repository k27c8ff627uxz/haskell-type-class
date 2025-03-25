{-# OPTIONS --prop #-}

module Elements.Types.Pair where

open import Agda.Primitive
open import Logic

record Pair {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B

open Pair public

assoc-Pair : {i j k : Level} → {A : Set i} → {B : Set j} → {C : Set k} → Pair (Pair A B) C → Pair A (Pair B C)
assoc-Pair {i} {j} {k} {A} {B} {C} ((a , b) , c) = (a , (b , c))
