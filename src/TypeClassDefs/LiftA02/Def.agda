{-# OPTIONS --prop #-}

module TypeClassDefs.LiftA02.Def where

open import Agda.Primitive
open import Logic
open import Elements

record LiftA02 {i : Level} (F : Set i → Set i) : Set (lsuc i) where
  field
    liftA0 : {A : Set i} → A → F A
    liftA2 : {A B C : Set i} → (A → B → C) → F A → F B → F C

  liftA1 : {A B : Set i} → (A → B) → F A → F B
  liftA1 {A} {B} f α = liftA2 (id (A → B)) (liftA0 f) α

  liftA3 : {A B C D : Set i} → (A → B → C → D) → F A → F B → F C → F D
  liftA3 {A} {B} {C} {D} f α β γ = liftA2 (id (C → D)) (liftA2 f α β) γ
  
  field
    LiftA2-Identity : {A : Set i} → liftA2 (id (A → A)) (liftA0 (id A)) ＝ id (F A)
    LiftA2-Homomorphism : {A B C : Set i} → (f : A → B → C) → (a : A) → (b : B) → liftA2 f (liftA0 a) (liftA0 b) ＝ liftA0 (f a b)
    LiftA2-Homomorphism-Left : {A B C : Set i} → (f : A → B → C) → (a : A) → (β : F B) → liftA2 f (liftA0 a) β ＝ liftA1 (\b → f a b) β
    LiftA2-Homomorphism-Right : {A B C : Set i} → (f : A → B → C) → (α : F A) → (b : B) → liftA2 f α (liftA0 b) ＝ liftA1 (\a → f a b) α
    LiftA1-to-LiftA2 : {A B C : Set i} → (f : A → B → C) → (α : F A) → (β : F B) → liftA2 (id (B → C)) (liftA1 f α) β ＝ liftA2 f α β
    LiftA2-LiftA2-Composition1 : {A B C D E : Set i} → (f : C → D → E) → (g : A → B → C) → (α : F A) → (β : F B) → (δ : F D) → liftA2 f (liftA2 g α β) δ ＝ liftA3 (\a → \b → \d → f (g a b) d) α β δ
    LiftA2-LiftA2-Composition2 : {A B C D E : Set i} → (f : C → D → E) → (g : A → B → D) → (α : F A) → (β : F B) → (γ : F C) → liftA2 f γ (liftA2 g α β) ＝ liftA3 (\c → \a → \b → f c (g a b)) γ α β

open LiftA02 public
