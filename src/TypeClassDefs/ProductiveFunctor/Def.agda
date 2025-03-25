{-# OPTIONS --prop #-}

module TypeClassDefs.ProductiveFunctor.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.FunctorWithUnit

record ProductiveFunctor {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    inherit-PFunctor : FunctorWithUnit F
    fpair : {A B : Set i} → F A → F B → F (Pair A B)

  pfmap : {A B : Set i} → (A → B) → F A → F B
  pfmap = ufmap inherit-PFunctor

  punit : {A : Set i} → A → F A
  punit = unit inherit-PFunctor
  
  field
    Fpair-Homomorphsm : {A B : Set i} → (a : A) → (b : B) → fpair (punit a) (punit b) ＝ punit ( a , b )
    Fpair-Commutative : {A B C : Set i} → (fa : F A) → (fb : F B) → (fc : F C) → pfmap (\p → assoc-Pair p) (fpair (fpair fa fb) fc) ＝ fpair fa (fpair fb fc)

open ProductiveFunctor public
