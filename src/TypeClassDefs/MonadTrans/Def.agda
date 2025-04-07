{-# OPTIONS --prop #-}

module TypeClassDefs.MonadTrans.Def where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.Monad

record MonadTrans {i} (T : {M : Set i → Set i} → Monad M → (Set i → Set i)): Set (lsuc i) where
  field
    MonadTrans-to-Monad : {M : Set i → Set i} → (monad : Monad M) → Monad (T monad)
    lift : {M : Set i → Set i} → {monad : Monad M} → {A : Set i} → M A → T monad A

  field
    MonadTrans-Return : {M : Set i → Set i} → {monad : Monad M} → {A : Set i} → (a : A) → return (MonadTrans-to-Monad monad) a ＝ lift (return monad a)
    MonadTrans-Bind : {M : Set i → Set i} → {monad : Monad M} → {A B : Set i} → (α : M A) → (f : A → M B) → lift (bind monad α f) ＝ bind (MonadTrans-to-Monad monad) (lift α) (\a → lift (f a))
