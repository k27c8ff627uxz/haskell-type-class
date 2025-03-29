{-# OPTIONS --prop #-}

module TypeClassDefs.Monad.Def where

open import Agda.Primitive
open import Logic
open import Elements

record Monad {i : Level} (F : Set i → Set i) : Set (lsuc i) where
  field
    return : {A : Set i} → A → F A
    bind : {A B : Set i} → F A → (A → F B) → F B

  field
    Return-Left-Identity : {A B : Set i} → (f : A → F B) → (a : A) → bind (return a) f ＝ f a
    Return-Right-Identity : {A : Set i} → (α : F A) → bind α return ＝ α 
    Bind-Composition : {A B C : Set i} → (f : A → F B) → (g : B → F C) → (α : F A) → bind (bind α f) g ＝ bind α (\a → bind (f a) g)

open Monad public
