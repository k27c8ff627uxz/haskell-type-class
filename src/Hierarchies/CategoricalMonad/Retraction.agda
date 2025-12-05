{-# OPTIONS --prop #-}

module Hierarchies.CategoricalMonad.Retraction where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Monad
open import Hierarchies.CategoricalMonad.Translates
open import Hierarchies.CategoricalMonad.Factors

retract-Monad-to-CategoricalMonad : {i : Level} → {F : Set i → Set i} → (cmonad : CategoricalMonad F) → Monad-to-CategoricalMonad (CategoricalMonad-to-Monad cmonad) ＝ cmonad
retract-Monad-to-CategoricalMonad {i} {F} cmonad =
  CategoricalMonad-Eq
    _
    cmonad
    (
      ＝-begin
        CategoricalMonad-to-FunctorWithUnit (Monad-to-CategoricalMonad (CategoricalMonad-to-Monad cmonad))
      ＝⟨ Monad-to-CategoricalMonad-to-FunctorWithUnit-Eq (CategoricalMonad-to-Monad cmonad) ⟩
        Monad-to-FunctorWithUnit (CategoricalMonad-to-Monad cmonad)
      ＝⟨ CategoricalMonad-to-Monad-to-FunctorWithUnit-Eq cmonad ⟩
        CategoricalMonad-to-FunctorWithUnit cmonad
      ＝-qed
    )
    (\A → fun-ext _ _ (\α →
      ＝-begin
        unions (Monad-to-CategoricalMonad (CategoricalMonad-to-Monad cmonad)) α
      ＝⟨⟩
        bind (CategoricalMonad-to-Monad cmonad) α (id (F A))
      ＝⟨⟩
        unions₀ (cmfmap₀ (id (F A)) α)
      ＝⟨ fun-eq (\x → unions₀ (x α)) (Fmap-Identity (FunctorWithUnit-to-Functor (CategoricalMonad-to-FunctorWithUnit cmonad))) ⟩
        unions₀ ((id (F (F A))) α)
      ＝⟨⟩
        unions₀ α
      ＝-qed
    ))
  where
    unions₀ : {A : Set i} → F (F A) → F A
    unions₀ = unions cmonad
    cmfmap₀ : {A B : Set i} → (A → B) → F A → F B
    cmfmap₀ = cmfmap cmonad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind (CategoricalMonad-to-Monad cmonad)



retract-CategoricalMonad-to-Monad : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → CategoricalMonad-to-Monad (Monad-to-CategoricalMonad monad) ＝ monad
retract-CategoricalMonad-to-Monad {i} {F} monad =
  Monad-Eq
    _
    _
    (\A → fun-ext _ _ (\a → ＝-refl _))
    (\A B → fun-ext _ _ (\α → fun-ext _ _ (\f →
      ＝-begin
        bind (CategoricalMonad-to-Monad (Monad-to-CategoricalMonad monad)) α f
      ＝⟨⟩
        unions cmonad₀ (cmfmap cmonad₀ f α)
      ＝⟨⟩
        bind₀ (bind₀ α (\a → return₀ (f a))) (id (F B))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (return₀ (f a)) (id (F B)))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → (id (F B)) (f a))
      ＝⟨⟩
        bind₀ α f
      ＝⟨⟩
        bind monad α f
      ＝-qed
    )))
  where
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    cmonad₀ : CategoricalMonad F
    cmonad₀ = Monad-to-CategoricalMonad monad
    
