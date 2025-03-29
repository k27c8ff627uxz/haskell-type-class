{-# OPTIONS --prop #-}

module TypeClassDefs.FunctorWithUnit.FunctorWithUnitRecordEqual where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.Functor
open import TypeClassDefs.FunctorWithUnit.Def

private
  record Body {i} (F : Set i → Set i) : Set (lsuc i) where
    field
      FunctorWithUnit-to-Functor : Functor F
      unit : {A : Set i} → A → F A

  record Conditions {i} {F : Set i → Set i} (body : Body F) : Prop (lsuc i) where
    FunctorWithUnit-to-Functor₀ : Functor F
    FunctorWithUnit-to-Functor₀ = Body.FunctorWithUnit-to-Functor body
    unit₀ : {A : Set i} → A → F A
    unit₀ = Body.unit body
    ufmap₀ : {A B : Set i} → (A → B) → F A → F B
    ufmap₀ = fmap FunctorWithUnit-to-Functor₀

    field
      Unit-Homomorphism : {A B : Set i} → (a : A) → (f : A → B) → ufmap₀ f (unit₀ a) ＝ unit₀ (f a)

  Body-Explicit : {i : Level} → {F : Set i → Set i} → (Functor F) → ((A : Set i) → A → F A) → Body F
  Body-Explicit {i} {F} functor-of-with-unit₀ unit₀ = record { FunctorWithUnit-to-Functor = functor-of-with-unit₀ ; unit = \{A : Set i} → unit₀ A }

  Body-Explicit-Eq : {i : Level} → {F : Set i → Set i} → (functor-of-with-unit₁ functor-of-with-unit₂ : Functor F) → (unit₁ unit₂ : (A : Set i) → A → F A) → functor-of-with-unit₁ ＝ functor-of-with-unit₂ → unit₁ ＝ unit₂ → Body-Explicit functor-of-with-unit₁ unit₁ ＝ Body-Explicit functor-of-with-unit₂ unit₂
  Body-Explicit-Eq
    functor-of-with-unit₀ functor-of-with-unit₀
    unit₀ unit₀
    (＝-refl functor-of-with-unit₀)
    (＝-refl unit₀)
    = ＝-refl _

  to-Body : {i : Level} → {F : Set i → Set i} → (functor-unit : FunctorWithUnit F) → Body F
  to-Body record { FunctorWithUnit-to-Functor = FunctorWithUnit-to-Functor₀ ; unit = unit₀ } = record { FunctorWithUnit-to-Functor = FunctorWithUnit-to-Functor₀ ; unit = unit₀ }

  to-Body-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (Body.FunctorWithUnit-to-Functor body₁ ＝ Body.FunctorWithUnit-to-Functor body₂) → ({A : Set i} → Body.unit body₁ {A} ＝ Body.unit body₂ {A}) → body₁ ＝ body₂
  to-Body-Eq
    {i} {F}
    record { FunctorWithUnit-to-Functor = functor₁ ; unit = unit₁ }
    record { FunctorWithUnit-to-Functor = functor₂ ; unit = unit₂ }
    eq-functor eq-unit
    = ＝-begin
      record { FunctorWithUnit-to-Functor = functor₁ ; unit = unit₁ }
    ＝⟨ ＝-refl _ ⟩
      Body-Explicit functor₁ (\A → unit₁ {A})
    ＝⟨
        Body-Explicit-Eq
          _ _ _ _
          eq-functor
          (fun-ext-dep _ _ (\A → eq-unit {A}))
      ⟩
      Body-Explicit functor₂ (\A → unit₂ {A})
    ＝⟨ ＝-refl _ ⟩
      record { FunctorWithUnit-to-Functor = functor₂ ; unit = unit₂ }
    ＝-qed
  
  to-Conditions : {i : Level} → {F : Set i → Set i} → (functor-unit : FunctorWithUnit F) → (Conditions (to-Body functor-unit))
  to-Conditions
    {i} {F}
    record { FunctorWithUnit-to-Functor = FunctorWithUnit-to-Functor₀ ; unit = unit₀ ; Unit-Homomorphism = Unit-Homomorphism₀ }
    = record { Unit-Homomorphism = Unit-Homomorphism₀}

  to-FunctorWithUnit : {i : Level} → {F : Set i → Set i} → (body : Body F) → (condition : Conditions body) → FunctorWithUnit F
  to-FunctorWithUnit {i} {F} record { FunctorWithUnit-to-Functor = FunctorWithUnit-to-Functor₀ ; unit = unit₀ } record { Unit-Homomorphism = Unit-Homomorphism₀ } =
    record { FunctorWithUnit-to-Functor = FunctorWithUnit-to-Functor₀ ; unit = unit₀ ; Unit-Homomorphism = Unit-Homomorphism₀ }

  FunctorWithUnit-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (functor-unit : FunctorWithUnit F) → functor-unit ＝ to-FunctorWithUnit (to-Body functor-unit) (to-Conditions functor-unit)
  FunctorWithUnit-to-FunctorWithUnit-Eq functor-unit = ＝-refl _

  to-FunctorWithUnit-Equal : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (condition₁ : Conditions body₁) → (condition₂ : Conditions body₂) → body₁ ＝ body₂ → to-FunctorWithUnit body₁ condition₁ ＝ to-FunctorWithUnit body₂ condition₂
  to-FunctorWithUnit-Equal
    body₁ body₂
    condition₁ condition₂
    eq-body
    = proof-irrelevance-with-type _ _ _ to-FunctorWithUnit body₁ body₂ condition₁ condition₂ eq-body

  FunctorWithUnit-Eq-Body : {i : Level} → {F : Set i → Set i} → (functor-unit₁ functor-unit₂ : FunctorWithUnit F) → (to-Body functor-unit₁ ＝ to-Body functor-unit₂) → functor-unit₁ ＝ functor-unit₂
  FunctorWithUnit-Eq-Body
    {i} {F}
    functor-unit₁ functor-unit₂
    eq-body
    = ＝-begin
      functor-unit₁
    ＝⟨ FunctorWithUnit-to-FunctorWithUnit-Eq functor-unit₁ ⟩
      to-FunctorWithUnit (to-Body functor-unit₁) (to-Conditions functor-unit₁)
    ＝⟨
        to-FunctorWithUnit-Equal
          (to-Body functor-unit₁)
          (to-Body functor-unit₂)
          (to-Conditions functor-unit₁)
          (to-Conditions functor-unit₂)
          eq-body
      ⟩
      to-FunctorWithUnit (to-Body functor-unit₂) (to-Conditions functor-unit₂)    
    ＝⟨- FunctorWithUnit-to-FunctorWithUnit-Eq functor-unit₂ ⟩
      functor-unit₂
    ＝-qed

  to-Body-Eq-From-FunctorWithUnit : {i : Level} → {F : Set i → Set i} → (functor-unit₁ functor-unit₂ : FunctorWithUnit F) → (FunctorWithUnit-to-Functor functor-unit₁ ＝ FunctorWithUnit-to-Functor functor-unit₂) → ({A : Set i} → unit functor-unit₁ {A} ＝ unit functor-unit₂ {A}) → to-Body functor-unit₁ ＝ to-Body functor-unit₂
  to-Body-Eq-From-FunctorWithUnit
    functor-unit₁ functor-unit₂
    eq-functor eq-unit
    = to-Body-Eq (to-Body functor-unit₁) (to-Body functor-unit₂) eq-functor eq-unit

FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (functor-unit₁ functor-unit₂ : FunctorWithUnit F) → (FunctorWithUnit-to-Functor functor-unit₁ ＝ FunctorWithUnit-to-Functor functor-unit₂) → ({A : Set i} → unit functor-unit₁ {A} ＝ unit functor-unit₂ {A}) → functor-unit₁ ＝ functor-unit₂
FunctorWithUnit-Eq
  functor-unit₁ functor-unit₂
  eq-functor eq-unit
  = FunctorWithUnit-Eq-Body functor-unit₁ functor-unit₂ (to-Body-Eq-From-FunctorWithUnit functor-unit₁ functor-unit₂ eq-functor eq-unit)
    
