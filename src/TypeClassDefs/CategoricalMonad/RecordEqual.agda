{-# OPTIONS --prop #-}

module TypeClassDefs.CategoricalMonad.RecordEqual where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.FunctorWithUnit
open import TypeClassDefs.CategoricalMonad.Def

private

  record Body {i} (F : Set i → Set i) : Set (lsuc i) where
    field
      CategoricalMonad-to-FunctorWithUnit : FunctorWithUnit F
      unions : {A : Set i} → F (F A) → F A

  Body-Explicit : {i : Level} → {F : Set i → Set i} → FunctorWithUnit F → ((A : Set i) → F (F A) → F A) → Body F
  Body-Explicit {i} {F} functor-with-unit₀ unions₀ = record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₀ ; unions = \{A : Set i} → unions₀ A }

  Body-Explicit-Eq : {i : Level} → {F : Set i → Set i} → (functor-with-unit₁ functor-with-unit₂ : FunctorWithUnit F) → (unions₁ unions₂ : (A : Set i) → F (F A) → F A) → functor-with-unit₁ ＝ functor-with-unit₂ → unions₁ ＝ unions₂ → Body-Explicit functor-with-unit₁ unions₁ ＝ Body-Explicit functor-with-unit₂ unions₂
  Body-Explicit-Eq {i} {F} functor-with-unit₀ functor-with-unit₀ unions₀ unions₀ (＝-refl functor-with-unit₀) (＝-refl unions₀) = ＝-refl _

  to-Body : {i : Level} → {F : Set i → Set i} → CategoricalMonad F → Body F
  to-Body record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₀ ; unions = unions₀ } = record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₀ ; unions = unions₀ }

  to-Body-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (Body.CategoricalMonad-to-FunctorWithUnit body₁ ＝ Body.CategoricalMonad-to-FunctorWithUnit body₂) → (∀{A : Set i} → Body.unions body₁ {A} ＝ Body.unions body₂ {A}) → body₁ ＝ body₂
  to-Body-Eq
    {i} {F}
    record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₁ ; unions = unions₁ }
    record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₂ ; unions = unions₂ }
    eq-functor-with-unit eq-unions
    = ＝-begin
      record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₁ ; unions = unions₁ }
    ＝⟨⟩
      Body-Explicit functor-with-unit₁ (\A → unions₁ {A})
    ＝⟨ Body-Explicit-Eq functor-with-unit₁ functor-with-unit₂ (\A → unions₁ {A}) (\A → unions₂ {A}) eq-functor-with-unit (fun-ext-dep _ _ (\A → eq-unions)) ⟩
      Body-Explicit functor-with-unit₂ (\A → unions₂ {A})
    ＝⟨⟩
      record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₂ ; unions = unions₂ }
    ＝-qed

  record Conditions {i} {F : Set i → Set i} (body : Body F) : Prop (lsuc i) where
    CategoricalMonad-to-FunctorWithUnit₀ : FunctorWithUnit F
    CategoricalMonad-to-FunctorWithUnit₀ = Body.CategoricalMonad-to-FunctorWithUnit body
    unions₀ : {A : Set i} → F (F A) → F A
    unions₀ = Body.unions body
    cunit₀ : {A : Set i} → A → F A
    cunit₀ = unit CategoricalMonad-to-FunctorWithUnit₀
    cmfmap₀ : {A B : Set i} → (A → B) → F A → F B
    cmfmap₀ = ufmap CategoricalMonad-to-FunctorWithUnit₀

    field
      unions-natural : {A B : Set i} → (f : A → B) → unions₀ ∘ (cmfmap₀ (cmfmap₀ f)) ＝ (cmfmap₀ f) ∘ unions₀
      cm-laxbicategory-comp : {A : Set i} → unions₀ ∘ unions₀ ＝ unions₀ ∘ (cmfmap₀ {F (F A)} unions₀)
      cm-laxbicategory-id-F : {A : Set i} → unions₀ ∘ (cmfmap₀ cunit₀) ＝ id (F A)
      cm-laxbicategory-id : {A : Set i} → unions₀ ∘ cunit₀ ＝ id (F A)

  to-Conditions : {i : Level} → {F : Set i → Set i} → (cmonad : CategoricalMonad F) → Conditions (to-Body cmonad)
  to-Conditions
    record { unions-natural = unions-natural₀ ; cm-laxbicategory-comp = cm-laxbicategory-comp₀ ; cm-laxbicategory-id-F = cm-laxbicategory-id-F₀ ; cm-laxbicategory-id = cm-laxbicategory-id₀ } =
    record { unions-natural = unions-natural₀ ; cm-laxbicategory-comp = cm-laxbicategory-comp₀ ; cm-laxbicategory-id-F = cm-laxbicategory-id-F₀ ; cm-laxbicategory-id = cm-laxbicategory-id₀ }

  to-CategoricalMonad : {i : Level} → {F : Set i → Set i} → (body : Body F) → (conditions : Conditions body) → CategoricalMonad F
  to-CategoricalMonad
    record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₀ ; unions = unions₀ }
    record { unions-natural = unions-natural₀ ; cm-laxbicategory-comp = cm-laxbicategory-comp₀ ; cm-laxbicategory-id-F = cm-laxbicategory-id-F₀ ; cm-laxbicategory-id = cm-laxbicategory-id₀ }
    = record { CategoricalMonad-to-FunctorWithUnit = functor-with-unit₀ ; unions = unions₀ ; unions-natural = unions-natural₀ ; cm-laxbicategory-comp = cm-laxbicategory-comp₀ ; cm-laxbicategory-id-F = cm-laxbicategory-id-F₀ ; cm-laxbicategory-id = cm-laxbicategory-id₀ }

  to-CategoricalMonad-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (conditions₁ : Conditions body₁) → (conditions₂ : Conditions body₂) → body₁ ＝ body₂ → to-CategoricalMonad body₁ conditions₁ ＝ to-CategoricalMonad body₂ conditions₂
  to-CategoricalMonad-Eq body₁ body₂ conditions₁ conditions₂ eq-body
    = proof-irrelevance-with-type _ _ _ to-CategoricalMonad body₁ body₂ conditions₁ conditions₂ eq-body

  CategoricalMonad-Eq-With-Body : {i : Level} → {F : Set i → Set i} → (cmonad₁ cmonad₂ : CategoricalMonad F) → to-Body cmonad₁ ＝ to-Body cmonad₂ → cmonad₁ ＝ cmonad₂
  CategoricalMonad-Eq-With-Body cmonad₁ cmonad₂ eq-body =
    ＝-begin
      cmonad₁
    ＝⟨⟩
      to-CategoricalMonad (to-Body cmonad₁) (to-Conditions cmonad₁)
    ＝⟨ to-CategoricalMonad-Eq (to-Body cmonad₁) (to-Body cmonad₂) (to-Conditions cmonad₁)(to-Conditions cmonad₂) eq-body ⟩
      to-CategoricalMonad (to-Body cmonad₂) (to-Conditions cmonad₂)
    ＝⟨⟩
      cmonad₂
    ＝-qed

CategoricalMonad-Eq : {i : Level} → {F : Set i → Set i} → (cmonad₁ cmonad₂ : CategoricalMonad F) → CategoricalMonad-to-FunctorWithUnit cmonad₁ ＝ CategoricalMonad-to-FunctorWithUnit cmonad₂ → ((A : Set i) → unions cmonad₁ {A} ＝ unions cmonad₂ {A}) → cmonad₁ ＝ cmonad₂
CategoricalMonad-Eq cmonad₁ cmonad₂ eq-functor-with-unit eq-unions =
  CategoricalMonad-Eq-With-Body
    cmonad₁
    cmonad₂
    (to-Body-Eq (to-Body cmonad₁) (to-Body cmonad₂) eq-functor-with-unit (\{A} → eq-unions A))
