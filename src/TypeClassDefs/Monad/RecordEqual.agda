{-# OPTIONS --prop #-}

module TypeClassDefs.Monad.RecordEqual where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.Monad.Def

private

  record Body {i} (F : Set i → Set i) : Set (lsuc i) where
    field
      return : {A : Set i} → A → F A
      bind : {A B : Set i} → F A → (A → F B) → F B


  Body-Explicit : {i : Level} → {F : Set i → Set i} → ((A : Set i) → A → F A) → ((A B : Set i) → F A → (A → F B) → F B) → Body F
  Body-Explicit {i} {F} return₀ bind₀ = record { return = \{A} → return₀ A ; bind = \{A B} → bind₀ A B }


  Body-Explicit-Eq : {i : Level} → {F : Set i → Set i} → (return₁ return₂ : (A : Set i) → A → F A) → (bind₁ bind₂ : (A B : Set i) → F A → (A → F B) → F B) → return₁ ＝ return₂ → bind₁ ＝ bind₂ → Body-Explicit return₁ bind₁ ＝ Body-Explicit return₂ bind₂
  Body-Explicit-Eq return₀ return₀ bind₀ bind₀ (＝-refl return₀) (＝-refl bind₀) = ＝-refl _


  to-Body : {i : Level} → {F : Set i → Set i} → Monad F → Body F
  to-Body record { return = return₀ ; bind = bind₀ } = record { return = return₀ ; bind = bind₀ }

  to-Body-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → ({A : Set i} → Body.return body₁ {A} ＝ Body.return body₂ {A}) → ({A B : Set i} → Body.bind body₁ {A} {B} ＝ Body.bind body₂ {A} {B}) → body₁ ＝ body₂
  to-Body-Eq
    {i} {F}
    record { return = return₁ ; bind = bind₁ }
    record { return = return₂ ; bind = bind₂ }
    eq-return eq-bind
    = ＝-begin
      record { return = return₁ ; bind = bind₁ }
    ＝⟨⟩
      Body-Explicit (\A → return₁ {A}) (\A B → bind₁ {A} {B})
    ＝⟨ Body-Explicit-Eq
          (\A → return₁ {A})
          (\A → return₂ {A})
          (\A B → bind₁ {A} {B})
          (\A B → bind₂ {A} {B})
          (fun-ext-dep _ _ (\A → eq-return {A}))
          (fun-ext-dep _ _ (\A → fun-ext-dep _ _ (\B → eq-bind {A} {B})))
      ⟩
      Body-Explicit (\A → return₂ {A}) (\A B → bind₂ {A} {B})
    ＝⟨⟩
      record { return = return₂ ; bind = bind₂ }
    ＝-qed


  record Conditions {i : Level} {F : Set i → Set i} (body : Body F) : Prop (lsuc i) where
    return' : {A : Set i} → A → F A
    return' = Body.return body
    bind' : {A B : Set i} → F A → (A → F B) → F B
    bind' = Body.bind body

    field
      Return-Left-Identity : {A B : Set i} → (f : A → F B) → (a : A) → bind' (return' a) f ＝ f a
      Return-Right-Identity : {A : Set i} → (α : F A) → bind' α return' ＝ α 
      Bind-Composition : {A B C : Set i} → (f : A → F B) → (g : B → F C) → (α : F A) → bind' (bind' α f) g ＝ bind' α (\a → bind' (f a) g)

  to-Conditions : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → Conditions (to-Body monad)
  to-Conditions
    record { return = return₀ ; bind = bind₀ ; Return-Left-Identity = Return-Left-Identity₀ ; Return-Right-Identity = Return-Right-Identity₀ ; Bind-Composition = Bind-Composition₀ }
    = record { Return-Left-Identity = Return-Left-Identity₀ ; Return-Right-Identity = Return-Right-Identity₀ ; Bind-Composition = Bind-Composition₀ }

  to-Monad : {i : Level} → {F : Set i → Set i} → (body : Body F) → (conditions : Conditions body) → Monad F
  to-Monad
    record { return = return₀ ; bind = bind₀ }
    record { Return-Left-Identity = Return-Left-Identity₀ ; Return-Right-Identity = Return-Right-Identity₀ ; Bind-Composition = Bind-Composition₀ }
    = record { return = return₀ ; bind = bind₀ ; Return-Left-Identity = Return-Left-Identity₀ ; Return-Right-Identity = Return-Right-Identity₀ ; Bind-Composition = Bind-Composition₀ }
  
  Monad-to-Monad-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → monad ＝ to-Monad (to-Body monad) (to-Conditions monad)
  Monad-to-Monad-Eq monad = ＝-refl _

  to-Monad-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (conditions₁ : Conditions body₁) → (conditions₂ : Conditions body₂) → body₁ ＝ body₂ → to-Monad body₁ conditions₁ ＝ to-Monad body₂ conditions₂
  to-Monad-Eq body₁ body₂ conditions₁ conditions₂ eq-body
    = proof-irrelevance-with-type _ _ _ to-Monad body₁ body₂ conditions₁ conditions₂ eq-body

  Monad-Eq-With-Body : {i : Level} → {F : Set i → Set i} → (monad₁ monad₂ : Monad F) → to-Body monad₁ ＝ to-Body monad₂ → monad₁ ＝ monad₂
  Monad-Eq-With-Body monad₁ monad₂ eq-body =
    ＝-begin
      monad₁
    ＝⟨ Monad-to-Monad-Eq monad₁ ⟩
      to-Monad (to-Body monad₁) (to-Conditions monad₁)
    ＝⟨ to-Monad-Eq (to-Body monad₁) (to-Body monad₂) (to-Conditions monad₁) (to-Conditions monad₂) eq-body ⟩
      to-Monad (to-Body monad₂) (to-Conditions monad₂)
    ＝⟨- Monad-to-Monad-Eq monad₂ ⟩
      monad₂
    ＝-qed


Monad-Eq : {i : Level} → {F : Set i → Set i} → (monad₁ monad₂ : Monad F) → ((A : Set i) → return monad₁ {A} ＝ return monad₂ {A}) → ((A B : Set i) → bind monad₁ {A} {B} ＝ bind monad₂ {A} {B}) → monad₁ ＝ monad₂
Monad-Eq monad₁ monad₂ eq-return eq-bind =
  Monad-Eq-With-Body
    monad₁
    monad₂
    (to-Body-Eq (to-Body monad₁) (to-Body monad₂) (\{A} → eq-return A) (\{A} {B} → eq-bind A B))
