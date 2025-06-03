{-# OPTIONS --prop #-}

module Instances.IdentType.Def where

open import Agda.Primitive

IdentType : {i : Level} → Set i → Set i
IdentType T = T

