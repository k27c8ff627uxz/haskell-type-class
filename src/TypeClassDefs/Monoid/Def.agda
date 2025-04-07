{-# OPTIONS --prop #-}

module TypeClassDefs.Monoid.Def where

open import Logic

record Monoid {i} (A : Set i) : Set i where
  field
    mempty : A
    mappend : A → A → A

  field
    Mempty-Left-Identity : (a : A) → mappend mempty a ＝ a
    Mempty-Right-Identity : (a : A) → mappend a mempty ＝ a
    Mappend-Assoc : (a b c : A) → mappend (mappend a b) c ＝ mappend a (mappend b c)

open Monoid public
