{-# OPTIONS --prop #-}

module Instances.IdentType.Classes where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Instances.IdentType.Def

IdentType-Monad : {i : Level} → Monad {i} IdentType
IdentType-Monad =
  record {
    return = id _
    ; bind = \a → \f → f a
    ; Return-Left-Identity = \f → \a → ＝-refl _
    ; Return-Right-Identity = \a → ＝-refl _
    ; Bind-Composition = \f → \g → \a → ＝-refl _
  }
