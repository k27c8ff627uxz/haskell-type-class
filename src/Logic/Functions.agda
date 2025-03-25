{-# OPTIONS --prop #-}

module Logic.Functions where

open import Agda.Primitive
open import Logic.Equality

module Equality where
  postulate fun-ext-dep : {i j : Level} → {A : Set i} {B : A → Set j} (f g : (a : A) → B a) → ((a : A) → f a ＝ g a) → f ＝ g

  fun-ext-dep-double : {i j : Level} → {A B X : Set i} {X : A → B → Set j} → (f g : (a : A) → (b : B) → X a b) → ((a : A) → (b : B) → f a b ＝ g a b) → f ＝ g
  fun-ext-dep-double {i} {j} {A} {B} {X} f g eqfg = fun-ext-dep f g λ a → fun-ext-dep _ _ λ b → eqfg a b
  
  fun-ext : {i j : Level} → {A : Set i} → {B : Set j} → (f g : A → B) → (∀(a : A) → f a ＝ g a) → f ＝ g
  fun-ext f g eqfg = fun-ext-dep f g eqfg

  fun-eq : {i j : Level} → {A : Set i} → {B : Set j} → (f : A → B) → {x y : A} → x ＝ y → f x ＝ f y
  fun-eq f {x} {x} (＝-refl x) = ＝-refl (f x)

open Equality public
