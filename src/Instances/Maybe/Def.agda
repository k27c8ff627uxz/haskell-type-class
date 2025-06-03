{-# OPTIONS --prop #-}

module Instances.Maybe.Def where

open import Agda.Primitive

data Maybe {i} (A : Set i) : Set i where
  Nothing : Maybe A
  Just : A → Maybe A

MaybeRec : {i j : Level} → {A : Set i} → {B : Set j} → (m : Maybe A) → (b : B) → (f : A → B) → B
MaybeRec Nothing b f = b
MaybeRec (Just a) b f = f a
