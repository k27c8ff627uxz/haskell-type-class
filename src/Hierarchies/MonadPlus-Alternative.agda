{-# OPTIONS --prop #-}

module Hierarchies.MonadPlus-Alternative where

open import Agda.Primitive
open import Logic
open import TypeClassDefs
open import Hierarchies.Monad-Applicative

MonadPlus-to-Alternative : {i : Level} → {F : Set i → Set i} → MonadPlus F → Alternative F
MonadPlus-to-Alternative {i} {F} monadplus =
  record { 
    Alternative-to-Applicative = applicative
    ; empty = empty₀
    ; or = or₀
    ; Empty-Identity-Left = MZero-Identity-Left monadplus
    ; Empty-Identity-Right = MZero-Identity-Right monadplus
    ; Or-Associative = MPlus-Associative monadplus
  }
  where
    applicative : Applicative F
    applicative = Monad-to-Applicative (MonadPlus-to-Monad monadplus)
    empty₀ : {A : Set i} → F A
    empty₀ = mzero monadplus
    or₀ : {A : Set i} → F A → F A → F A
    or₀ = mplus monadplus
