{-# OPTIONS --prop #-}

module Hierarchies.CategoricalMonad.Translates where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Monad

Monad-to-CategoricalMonad : {i : Level} → {F : Set i → Set i} → Monad F → CategoricalMonad F
Monad-to-CategoricalMonad {i} {F} monad =
  record {
    CategoricalMonad-to-FunctorWithUnit = CategoricalMonad-to-FunctorWithUnit₀
    ; unions = unions₀
    ; unions-natural = \{A} {B} → \f → fun-ext _ _ (\α →
      ＝-begin
        (unions₀ ∘ (cmfmap₀ (cmfmap₀ f))) α
      ＝⟨⟩
        unions₀ (cmfmap₀ (cmfmap₀ f) α)
      ＝⟨⟩
        bind₀ (fmap₀ (fmap₀ f) α) (id (F B))
      ＝⟨⟩
        bind₀ (bind₀ α (\a' → return₀ (fmap₀ f a'))) (id (F B))
      ＝⟨⟩
        bind₀ (bind₀ α (\a' → return₀ (bind₀ a' (\a → return₀ (f a))))) (id (F B))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a' → bind₀ (return₀ (bind₀ a' (\a → return₀ (f a)))) (id (F B)))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\α → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a' → (id (F B)) (bind₀ a' (\a → return₀ (f a))))
      ＝⟨⟩
        bind₀ α (\a' → bind₀ a' (\a → return₀ (f a)))
      ＝⟨⟩
        bind₀ α (\a' → bind₀ ((id (F A)) a') (\a → return₀ (f a)))
      ＝⟨- Bind-Composition monad _ _ _ ⟩
        bind₀ (bind₀ α (id (F A))) (\a → return₀ (f a))
      ＝⟨⟩
        fmap₀ f (bind₀ α (id (F A)))
      ＝⟨⟩
        (cmfmap₀ f) (unions₀ α)
      ＝⟨⟩
        ((cmfmap₀ f) ∘ unions₀) α
      ＝-qed
    )
    ; cm-laxbicategory-comp = \{A} → fun-ext _ _ (\α →
      ＝-begin
        (unions₀ ∘ unions₀) α
      ＝⟨⟩
        unions₀ (unions₀ α)
      ＝⟨⟩
        unions₀ (bind₀ α (id (F (F A))))
      ＝⟨⟩
        bind₀ (bind₀ α (id (F (F A)))) (id (F A))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ ((id (F (F A))) a) (id (F A)))
      ＝⟨⟩
        bind₀ α (\a → bind₀ a (id (F A)))
      ＝⟨⟩
        bind₀ α (\a → unions₀ a)
      ＝⟨⟩
        bind₀ α (\a → (id (F A)) (unions₀ a))
      ＝⟨- fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → bind₀ (return₀ (unions₀ a)) (id (F A)))
      ＝⟨- Bind-Composition monad _ _ _ ⟩
        bind₀ (bind₀ α (\a → return₀ (unions₀ a))) (id (F A))
      ＝⟨⟩
        bind₀ (fmap₀ unions₀ α) (id (F A))
      ＝⟨⟩
        unions₀ (cmfmap₀ unions₀ α)
      ＝⟨⟩
        (unions₀ ∘ cmfmap₀ unions₀) α
      ＝-qed
    )
    ; cm-laxbicategory-id-F = \{A} → fun-ext _ _ (\α →
      ＝-begin
        (unions₀ ∘ (cmfmap₀ cunit₀)) α
      ＝⟨⟩
        unions₀ (cmfmap₀ cunit₀ α)
      ＝⟨⟩
        unions₀ (bind₀ α (\a → return₀ (return₀ a)))
      ＝⟨⟩
        bind₀ (bind₀ α (\a → return₀ (return₀ a))) (id (F A))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (return₀ (return₀ a)) (id (F A)))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → (id (F A)) (return₀ a))
      ＝⟨⟩
        bind₀ α (\a → return₀ a)
      ＝⟨⟩
        bind₀ α return₀
      ＝⟨ Return-Right-Identity monad _ ⟩
        α
      ＝⟨⟩
        (id (F A)) α
      ＝-qed
    )
    ; cm-laxbicategory-id = \{A} → fun-ext _ _ (\α →
      ＝-begin
        (unions₀ ∘ cunit₀) α
      ＝⟨⟩
        unions₀ (cunit₀ α)
      ＝⟨⟩
        bind₀ (return₀ α) (id (F A))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        (id (F A)) α
      ＝-qed
    )
  } where
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    CategoricalMonad-to-FunctorWithUnit₀ : FunctorWithUnit F
    CategoricalMonad-to-FunctorWithUnit₀ = Monad-to-FunctorWithUnit monad
    unions₀ : {A : Set i} → F (F A) → F A
    unions₀ {A} α = bind₀ α (id (F A))
    cunit₀ : {A : Set i} → A → F A
    cunit₀ = unit CategoricalMonad-to-FunctorWithUnit₀
    cmfmap₀ : {A B : Set i} → (A → B) → F A → F B
    cmfmap₀ = ufmap CategoricalMonad-to-FunctorWithUnit₀
    fmap₀ : {A B : Set i} → (A → B) → F A → F B
    fmap₀ = fmap (Monad-to-Functor monad)


CategoricalMonad-to-Monad : {i : Level} → {F : Set i → Set i} → CategoricalMonad F → Monad F
CategoricalMonad-to-Monad {i} {F} cmonad =
  record {
    return = return₀
    ; bind = bind₀
    ; Return-Left-Identity = \{A} {B} → \f → \a →
      ＝-begin
        bind₀ (return₀ a) f
      ＝⟨⟩
        unions₀ (fmap₀ f (return₀ a))
      ＝⟨ fun-eq (\x → unions₀ x) (Unit-Homomorphism CategoricalMonad-to-FunctorWithUnit₀ _ _) ⟩
        unions₀ (return₀ (f a))
      ＝⟨⟩
        (unions₀ ∘ return₀) (f a)
      ＝⟨ fun-eq (\x → x (f a)) (cm-laxbicategory-id cmonad) ⟩
        (id (F B)) (f a)
      ＝⟨⟩
        f a
      ＝-qed
    ; Return-Right-Identity = \{A} → \α →
      ＝-begin
        bind₀ α return₀
      ＝⟨⟩
        unions₀ (fmap₀ return₀ α)
      ＝⟨⟩
        (unions₀ ∘ (fmap₀ return₀)) α
      ＝⟨ fun-eq (\x → x α) (cm-laxbicategory-id-F cmonad) ⟩
        (id (F A)) α
      ＝⟨⟩
        α
      ＝-qed
    ; Bind-Composition = \{A B C} → \f → \g → \α →
      ＝-begin
        bind₀ (bind₀ α f) g
      ＝⟨⟩
        unions₀ (fmap₀ g (unions₀ (fmap₀ f α)))
      ＝⟨⟩
        unions₀ (((fmap₀ g) ∘ unions₀) (fmap₀ f α))
      ＝⟨- fun-eq (\x → unions₀ (x (fmap₀ f α))) (unions-natural cmonad g) ⟩
        unions₀ ((unions₀ ∘ (fmap₀ (fmap₀ g))) (fmap₀ f α))
      ＝⟨⟩
        unions₀ (unions₀ (fmap₀ (fmap₀ g) (fmap₀ f α)))
      ＝⟨⟩
        (unions₀ ∘ unions₀) (fmap₀ (fmap₀ g) (fmap₀ f α))
      ＝⟨ fun-eq (\x → x (fmap₀ (fmap₀ g) (fmap₀ f α))) (cm-laxbicategory-comp cmonad) ⟩
        (unions₀ ∘ (fmap₀ unions₀)) (fmap₀ (fmap₀ g) (fmap₀ f α))
      ＝⟨⟩
        unions₀ (fmap₀ unions₀ (fmap₀ (fmap₀ g) (fmap₀ f α)))
      ＝⟨ fun-eq (\x → unions₀ x) (
        ＝-begin
          fmap₀ unions₀ (fmap₀ (fmap₀ g) (fmap₀ f α))
        ＝⟨⟩
          ((fmap₀ unions₀) ∘ (fmap₀ (fmap₀ g))) (fmap₀ f α)
        ＝⟨- fun-eq (\x → x (fmap₀ f α)) (Fmap-Composition CategoricalMonad-to-Functor₀) ⟩
          fmap₀ (unions₀ ∘ (fmap₀ g)) (fmap₀ f α)
        ＝⟨⟩
          fmap₀ (\a → unions₀ (fmap₀ g a)) (fmap₀ f α)
        ＝⟨⟩
          ((fmap₀ (\a → unions₀ (fmap₀ g a))) ∘ (fmap₀ f)) α
        ＝⟨- fun-eq (\x → x α) (Fmap-Composition CategoricalMonad-to-Functor₀) ⟩
          fmap₀ ((\a → unions₀ (fmap₀ g a)) ∘ f) α
        ＝⟨⟩
          fmap₀ (\a → unions₀ (fmap₀ g (f a))) α
        ＝-qed
        )⟩
        unions₀ (fmap₀ (\a → unions₀ (fmap₀ g (f a))) α)
      ＝⟨⟩
        bind₀ α (\a → bind₀ (f a) g)
      ＝-qed
  } where
    CategoricalMonad-to-FunctorWithUnit₀ : FunctorWithUnit F
    CategoricalMonad-to-FunctorWithUnit₀ = CategoricalMonad-to-FunctorWithUnit cmonad
    CategoricalMonad-to-Functor₀ : Functor F
    CategoricalMonad-to-Functor₀ = FunctorWithUnit-to-Functor CategoricalMonad-to-FunctorWithUnit₀
    unions₀ : {A : Set i} → F (F A) → F A
    unions₀ = unions cmonad
    return₀ : {A : Set i} → A → F A
    return₀ = cunit cmonad
    fmap₀ : {A B : Set i} → (A → B) → F A → F B
    fmap₀ = cmfmap cmonad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ α f = unions₀ (fmap₀ f α)

CategoricalMonad-to-Functor : {i : Level} → {F : Set i → Set i} → CategoricalMonad F → Functor F
CategoricalMonad-to-Functor cmonad = FunctorWithUnit-to-Functor (CategoricalMonad-to-FunctorWithUnit cmonad)
