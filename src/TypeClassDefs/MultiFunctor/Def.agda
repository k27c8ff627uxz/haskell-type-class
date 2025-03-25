{-# OPTIONS --prop #-}

module TypeClassDefs.MultiFunctor.Def where

open import Agda.Primitive
open import Logic
open import Elements

record MultiFunctor {i} (F : Set i → Set i) : Set (lsuc (lsuc i)) where
  field
    fmapn : {ltype : List (Set i)} → {A : Set i} → (f : (TypedList ltype) → A) → (TypedList (list-fmap F ltype)) → F A 

  field
    Fmapn-Identity : {A : Set i} → fmapn (id-TypedList A) ＝ id-TypedList (F A)
    Fmapn-Composition : {typed₁ typed₂ : List (Set i)} → {A B : Set i} → (f : TypedList (A ∷ typed₂) → B) → (g : TypedList typed₁ → A) → (list₁ : TypedList (list-fmap F typed₁)) → (list₂ : TypedList (list-fmap F typed₂)) → fmapn { typed₁ ⧺ typed₂ } (composition-TypedList {i} {typed₁} {typed₂} f g) (fmap-t++-homomorphism typed₁ typed₂ (list₁ t++ list₂)) ＝ fmapn f ((fmapn g list₁) t∷ list₂)

open MultiFunctor public
