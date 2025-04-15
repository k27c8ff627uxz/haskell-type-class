{-# OPTIONS --prop #-}

module TypeClassDefs.FoldrFoldable.Def where

open import Agda.Primitive

record FoldrFoldable {i} (T : Set i → Set i) : Set (lsuc i) where
  field
    foldr : {A B : Set i} → (A → B → B) → B → T A → B
    
open FoldrFoldable public
