{-# OPTIONS --prop #-}

module Instances.MaybeT.Def where

open import Agda.Primitive
open import TypeClassDefs
open import Instances.Maybe

MaybeT : {i : Level} → {M : Set i → Set i} → (monad : Monad M) → (A : Set i) → Set i
MaybeT {i} {M} _ A = M (Maybe A)
