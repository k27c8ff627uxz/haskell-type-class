{-# OPTIONS --prop #-}

module Hierarchies.Monad.Factor-toFunctor where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Applicative
open import Hierarchies.Monad.Translates

Monad-to-FunctorWithUnit-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → FunctorWithUnit-to-Functor (Monad-to-FunctorWithUnit monad) ＝ Monad-to-Functor monad
Monad-to-FunctorWithUnit-to-Functor-Eq {i} {F} monad = ＝-refl _

Monad-to-Applicative-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → Applicative-to-Functor (Monad-to-Applicative monad) ＝ Monad-to-Functor monad
Monad-to-Applicative-to-Functor-Eq {i} {F} monad =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\(f : A → B) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        fmap (Applicative-to-Functor applicative) f α
      ＝⟨⟩
        ap applicative (pure applicative f) α
      ＝⟨⟩
        bind₀ (return₀ f) (\f' → bind₀ α (\a → return₀ (f' a)))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ α (\a → return₀ (f a))
      ＝⟨⟩
        fmap (Monad-to-Functor monad) f α
      ＝-qed
    ))) where
      applicative : Applicative F
      applicative = Monad-to-Applicative monad
      return₀ : {A : Set i} → A → F A
      return₀ = return monad
      bind₀ : {A B : Set i} → F A → (A → F B) → F B
      bind₀ = bind monad

Monad-to-Applicative-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → Applicative-to-FunctorWithUnit (Monad-to-Applicative monad) ＝ Monad-to-FunctorWithUnit monad
Monad-to-Applicative-to-FunctorWithUnit-Eq {i} {F} monad =
  FunctorWithUnit-Eq
    _
    _
    (
      ＝-begin
        FunctorWithUnit-to-Functor (Applicative-to-FunctorWithUnit (Monad-to-Applicative monad))
      ＝⟨⟩
        Applicative-to-Functor (Monad-to-Applicative monad)
      ＝⟨ Monad-to-Applicative-to-Functor-Eq monad ⟩
        Monad-to-Functor monad
      ＝⟨- Monad-to-FunctorWithUnit-to-Functor-Eq monad ⟩
        FunctorWithUnit-to-Functor (Monad-to-FunctorWithUnit monad)
      ＝-qed
    )
    (\{A} → ＝-refl _)

Monad-to-LiftA02-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → LiftA02-to-Functor (Monad-to-LiftA02 monad) ＝ Monad-to-Functor monad
Monad-to-LiftA02-to-Functor-Eq {i} {F} monad =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\(f : A → B) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        fmap (LiftA02-to-Functor lifta02) f α
      ＝⟨⟩
        liftA2 lifta02 (id (A → B)) (liftA0 lifta02 f) α
      ＝⟨⟩
        bind₀ (return₀ f) (\f' → bind₀ α (\a → return₀ ((id (A → B)) f' a)))
      ＝⟨⟩
        bind₀ (return₀ f) (\f' → bind₀ α (\a → return₀ (f' a)))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ α (\a → return₀ (f a))
      ＝⟨⟩
        fmap (Monad-to-Functor monad) f α
      ＝-qed
    ))) where
      lifta02 : LiftA02 F
      lifta02 = Monad-to-LiftA02 monad
      return₀ : {A : Set i} → A → F A
      return₀ = return monad
      bind₀ : {A B : Set i} → F A → (A → F B) → F B
      bind₀ = bind monad

Monad-to-LiftA02-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → LiftA02-to-FunctorWithUnit (Monad-to-LiftA02 monad) ＝ Monad-to-FunctorWithUnit monad
Monad-to-LiftA02-to-FunctorWithUnit-Eq {i} {F} monad =
  FunctorWithUnit-Eq
    _
    _
    (
      ＝-begin
        FunctorWithUnit-to-Functor (LiftA02-to-FunctorWithUnit (Monad-to-LiftA02 monad))
      ＝⟨⟩
        LiftA02-to-Functor (Monad-to-LiftA02 monad)
      ＝⟨ Monad-to-LiftA02-to-Functor-Eq monad ⟩
        Monad-to-Functor monad
      ＝⟨- Monad-to-FunctorWithUnit-to-Functor-Eq monad ⟩
        FunctorWithUnit-to-Functor (Monad-to-FunctorWithUnit monad)
      ＝-qed
    )
    (\{A} → ＝-refl _)

Monad-to-ProductiveFunctor-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → ProductiveFunctor-to-FunctorWithUnit (Monad-to-ProductiveFunctor monad) ＝ Monad-to-FunctorWithUnit monad
Monad-to-ProductiveFunctor-to-FunctorWithUnit-Eq {i} {F} monad =
  FunctorWithUnit-Eq
    _
    _
    (
      ＝-begin
        FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit (Monad-to-ProductiveFunctor monad))
      ＝⟨⟩
        Monad-to-Functor monad
      ＝⟨- Monad-to-FunctorWithUnit-to-Functor-Eq monad ⟩
        FunctorWithUnit-to-Functor (Monad-to-FunctorWithUnit monad)
      ＝-qed
    )
    (\{A} → ＝-refl _)

Monad-to-ProductiveFunctor-to-Functor : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → ProductiveFunctor-to-Functor (Monad-to-ProductiveFunctor monad) ＝ Monad-to-Functor monad
Monad-to-ProductiveFunctor-to-Functor {i} {F} monad =
  ＝-begin
    ProductiveFunctor-to-Functor (Monad-to-ProductiveFunctor monad)
  ＝⟨⟩
    FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit (Monad-to-ProductiveFunctor monad))
  ＝⟨ fun-eq (\x → FunctorWithUnit-to-Functor x) (Monad-to-ProductiveFunctor-to-FunctorWithUnit-Eq monad) ⟩
    FunctorWithUnit-to-Functor (Monad-to-FunctorWithUnit monad)
  ＝⟨ Monad-to-FunctorWithUnit-to-Functor-Eq monad ⟩
    Monad-to-Functor monad
  ＝-qed
