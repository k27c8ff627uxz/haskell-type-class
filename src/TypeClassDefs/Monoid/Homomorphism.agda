{-# OPTIONS --prop #-}

module TypeClassDefs.Monoid.Homomorphism where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Monoid.Def

record MonoidHomomorphism {i} {A : Set i} {B : Set i} (monoidA : Monoid A) (monoidB : Monoid B) (f : A → B): Prop (lsuc i) where
  field
    MonoidHomomorphism-Empty : f (mempty monoidA) ＝ mempty monoidB
    MonoidHomomorphism-Append : ∀(x y : A) → f (mappend monoidA x y) ＝ mappend monoidB (f x) (f y)

open MonoidHomomorphism public

Id-MonoidHomomorphism : {i : Level} → {M : Set i} → (monoid : Monoid M) → MonoidHomomorphism monoid monoid (id M)
Id-MonoidHomomorphism {M} monoid
  = record {
      MonoidHomomorphism-Empty = ＝-refl _
      ; MonoidHomomorphism-Append = \x y → ＝-refl _
    }
