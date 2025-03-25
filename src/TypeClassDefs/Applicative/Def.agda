{-# OPTIONS --prop #-}

module TypeClassDefs.Applicative.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Functor

record Applicative {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    pure : ∀{A} → A → F A
    ap : ∀{A B : Set i} → F (A → B) → F A → F B

  afmap : {A B : Set i} → (A → B) → F A → F B
  afmap f = ap (pure f)
  
  field
    Ap-Identity : ∀{A} → ap (pure (id A)) ＝ id (F A)
    Ap-Composition : ∀{A B C} → (u : F (B → C)) → (v : F (A → B)) → (w : F A) → (ap (ap (ap (pure _∘_) u) v) w) ＝ (ap u (ap v w))
    Ap-Homomorphism : ∀{A B} → (f : A → B) → (x : A) → ap (pure f) (pure x) ＝ pure (f x)
    Ap-Interchange : ∀{A B} → (u : F (A → B)) → (y : A) → ap u (pure y) ＝ ap (pure (\f → f y)) u

open Applicative public
