{-# OPTIONS --prop #-}

module Hierarchies.CategoricalMonad.Factors where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Monad
open import Hierarchies.CategoricalMonad.Translates

Monad-to-CategoricalMonad-to-FunctorWithUnit-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → FunctorWithUnit-to-Functor (CategoricalMonad-to-FunctorWithUnit (Monad-to-CategoricalMonad monad)) ＝ Monad-to-Functor monad
Monad-to-CategoricalMonad-to-FunctorWithUnit-to-Functor-Eq {i} {F} monad =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\f → fun-ext _ _ (\α → ＝-refl _)))

Monad-to-CategoricalMonad-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → CategoricalMonad-to-FunctorWithUnit (Monad-to-CategoricalMonad monad) ＝ Monad-to-FunctorWithUnit monad
Monad-to-CategoricalMonad-to-FunctorWithUnit-Eq {i} {F} monad =
  FunctorWithUnit-Eq
    _
    _
    (Monad-to-CategoricalMonad-to-FunctorWithUnit-to-Functor-Eq monad)
    (\{A} → fun-ext _ _ (\a → ＝-refl _))

CategoricalMonad-to-Monad-to-FunctorWithUnit-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (cmonad : CategoricalMonad F) → FunctorWithUnit-to-Functor (Monad-to-FunctorWithUnit (CategoricalMonad-to-Monad cmonad)) ＝ CategoricalMonad-to-Functor cmonad
CategoricalMonad-to-Monad-to-FunctorWithUnit-to-Functor-Eq {i} {F} cmonad =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\f → fun-ext _ _ (\α →
      ＝-begin
        fmap (FunctorWithUnit-to-Functor (Monad-to-FunctorWithUnit (CategoricalMonad-to-Monad cmonad))) f α
      ＝⟨⟩
        bind monad₀ α (\a → return monad₀ (f a))
      ＝⟨⟩
        unions₀ (fmap₀ (\a → cunit₀ (f a)) α)
      ＝⟨⟩
        unions₀ (fmap₀ (cunit₀ ∘ f) α)
      ＝⟨ fun-eq (\x → unions₀ (x α)) (Fmap-Composition functor₀) ⟩
        unions₀ (((fmap₀ cunit₀) ∘ (fmap₀ f)) α)
      ＝⟨⟩
        (unions₀ ∘ (fmap₀ cunit₀)) (fmap₀ f α)
      ＝⟨ fun-eq (\x → x (fmap₀ f α)) (cm-laxbicategory-id-F cmonad) ⟩
        (id (F B)) (fmap₀ f α)
      ＝⟨⟩
        fmap₀ f α
      ＝⟨⟩
        fmap (CategoricalMonad-to-Functor cmonad) f α
      ＝-qed
    )))
    where
      monad₀ : Monad F
      monad₀ = CategoricalMonad-to-Monad cmonad
      unions₀ : {A : Set i} → F (F A) → F A
      unions₀ = unions cmonad
      cunit₀ : {A : Set i} → A → F A
      cunit₀ = cunit cmonad
      functor₀ : Functor F
      functor₀ = CategoricalMonad-to-Functor cmonad
      fmap₀ : {A B : Set i} → (A → B) → F A → F B
      fmap₀ = fmap functor₀

CategoricalMonad-to-Monad-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (cmonad : CategoricalMonad F) → Monad-to-FunctorWithUnit (CategoricalMonad-to-Monad cmonad) ＝ CategoricalMonad-to-FunctorWithUnit cmonad
CategoricalMonad-to-Monad-to-FunctorWithUnit-Eq {i} {F} cmonad =
  FunctorWithUnit-Eq
    _
    _
    (CategoricalMonad-to-Monad-to-FunctorWithUnit-to-Functor-Eq cmonad)
    (\{A} → ＝-refl _)
