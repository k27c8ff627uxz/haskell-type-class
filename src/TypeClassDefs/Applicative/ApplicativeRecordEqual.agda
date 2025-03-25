{-# OPTIONS --prop #-}

module TypeClassDefs.Applicative.ApplicativeRecordEqual where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Applicative.Def

private
  record Body {i} (F : Set i → Set i) : Set (lsuc i) where
    field
      pure : ∀{A : Set i} → A → F A
      ap : ∀{A B : Set i} → F (A → B) → F A → F B

  record Conditions {i} {F : Set i → Set i} (body : Body F) : Prop (lsuc i) where
    pure₀ : ∀{A} → A → F A
    pure₀ = Body.pure body
    ap₀ : ∀{A B : Set i} → F (A → B) → F A → F B
    ap₀  = Body.ap body
    field
      Ap-Identity : ∀{A} → ap₀ (pure₀ (id A)) ＝ id (F A)
      Ap-Composition : ∀{A B C} → (u : F (B → C)) → (v : F (A → B)) → (w : F A) → (ap₀ (ap₀ (ap₀ (pure₀ _∘_) u) v) w) ＝ (ap₀ u (ap₀ v w))
      Ap-Homomorphism : ∀{A B} → (f : A → B) → (x : A) → ap₀ (pure₀ f) (pure₀ x) ＝ pure₀ (f x)
      Ap-Interchange : ∀{A B} → (u : F (A → B)) → (y : A) → ap₀ u (pure₀ y) ＝ ap₀ (pure₀ (\f → f y)) u

  Body-Explicit : {i : Level} → {F : Set i → Set i} → ((A : Set i) → A → F A) → ((A B : Set i) → F (A → B) → F A → F B) → Body F
  Body-Explicit {i} {F} pure₀ ap₀ = record { pure = \{A : Set i} → pure₀ A ; ap = \{A B : Set i} → ap₀ A B }

  Body-Explicit-Eq : {i : Level} → {F : Set i → Set i} → (pure₁ pure₂ : (A : Set i) → A → F A) → (ap₁ ap₂ : (A B : Set i) → F (A → B) → F A → F B) → pure₁ ＝ pure₂ → ap₁ ＝ ap₂ → Body-Explicit pure₁ ap₁ ＝ Body-Explicit pure₂ ap₂
  Body-Explicit-Eq
    {i} {F}
    pure₀ pure₀
    ap₀ ap₀
    (＝-refl pure₀)
    (＝-refl ap₀)
    = ＝-refl _
    
  to-Body : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → Body F
  to-Body
    record { pure = pure₀ ; ap = ap₀ } =
      record { pure = pure₀ ; ap = ap₀ }

  
  to-Body-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → ({A : Set i} → Body.pure body₁ {A} ＝ Body.pure body₂ {A}) → (∀{A B : Set i} → Body.ap body₁ {A} {B} ＝ Body.ap body₂ {A} {B}) → body₁ ＝ body₂
  to-Body-Eq
    {i} {F}
    record { pure = pure₁ ; ap = ap₁ }
    record { pure = pure₂ ; ap = ap₂ }
    eq-pure eq-ap =
    ＝-begin
      record { pure = pure₁ ; ap = ap₁ }
    ＝⟨ ＝-refl _ ⟩
      Body-Explicit (\(A : Set i) → pure₁ {A}) (\(A B : Set i) → ap₁ {A} {B})
    ＝⟨
        Body-Explicit-Eq
          _ _ _ _
          (fun-ext-dep _ _ (\A → eq-pure {A}))
          (fun-ext-dep _ _ (\A → fun-ext-dep _ _ (\B → eq-ap {A} {B})))
      ⟩
      Body-Explicit (\(A : Set i) → pure₂ {A}) (\(A B : Set i) → ap₂ {A} {B})
    ＝⟨ ＝-refl _ ⟩
      record { pure = pure₂ ; ap = ap₂ }
    ＝-qed
  
  to-Conditions : {i :  Level} → {F : Set i → Set i} → (applicative : Applicative F) → Conditions (to-Body applicative)
  to-Conditions
    record {
      pure = pure₀ ; ap = ap₀ ;
      Ap-Identity = Ap-Identity₀ ; Ap-Composition = Ap-Composition₀ ; Ap-Homomorphism = Ap-Homomorphism₀ ; Ap-Interchange = Ap-Interchange₀
    } =
      record
        { Ap-Identity = Ap-Identity₀
        ; Ap-Composition = Ap-Composition₀
        ; Ap-Homomorphism = Ap-Homomorphism₀
        ; Ap-Interchange = Ap-Interchange₀
        }

  to-Applicative : {i : Level} → {F : Set i → Set i} → (body : Body F) → (condition : Conditions body) → Applicative F
  to-Applicative
    record { pure = pure₀ ; ap = ap₀ }
    record { Ap-Identity = Ap-Identity₀ ; Ap-Composition = Ap-Composition₀ ; Ap-Homomorphism = Ap-Homomorphism₀ ; Ap-Interchange = Ap-Interchange₀ }
      = record
          { pure = pure₀
          ; ap = ap₀
          ; Ap-Identity = Ap-Identity₀
          ; Ap-Composition = Ap-Composition₀
          ; Ap-Homomorphism = Ap-Homomorphism₀
          ; Ap-Interchange = Ap-Interchange₀
          }

  Applicative-to-Applicative-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → applicative ＝ to-Applicative (to-Body applicative) (to-Conditions applicative)
  Applicative-to-Applicative-Eq {i} {F} applicative = ＝-refl _

  to-Applicative-Equal : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (condition₁ : Conditions body₁) → (condition₂ : Conditions body₂) → body₁ ＝ body₂ → to-Applicative body₁ condition₁ ＝ to-Applicative body₂ condition₂
  to-Applicative-Equal
    body₁ body₂
    condition₁ condition₂
    eq-body =
      proof-irrelevance-with-type _ _ _ to-Applicative body₁ body₂ condition₁ condition₂ eq-body


  Applicative-Eq-With-Body : {i : Level} → {F : Set i → Set i} → (applicative₁ applicative₂ : Applicative F) → (to-Body applicative₁ ＝ to-Body applicative₂) → applicative₁ ＝ applicative₂
  Applicative-Eq-With-Body
    {i} {F}
    applicative₁
    applicative₂
    eq-body
    =
    ＝-begin
      applicative₁
    ＝⟨ Applicative-to-Applicative-Eq applicative₁ ⟩
      to-Applicative (to-Body applicative₁) (to-Conditions applicative₁)
    ＝⟨ to-Applicative-Equal _ _ (to-Conditions applicative₁) (to-Conditions applicative₂) eq-body ⟩
      to-Applicative (to-Body applicative₂) (to-Conditions applicative₂)
    ＝⟨- Applicative-to-Applicative-Eq applicative₂ ⟩
      applicative₂
    ＝-qed
    

  to-Body-Eq-From-Applicative : {i : Level} → {F : Set i → Set i} → (applicative₁ applicative₂ : Applicative F) → (∀{A : Set i} → pure applicative₁ {A} ＝ pure applicative₂ {A}) → (∀{A B : Set i} → ap applicative₁ {A} {B} ＝ ap applicative₂ {A} {B}) → to-Body applicative₁ ＝ to-Body applicative₂
  to-Body-Eq-From-Applicative
    {i} {F}
    applicative₁
    applicative₂
    eq-pure
    eq-ap =
      to-Body-Eq
        (to-Body applicative₁) (to-Body applicative₂)
        eq-pure eq-ap


Applicative-Eq : {i : Level} → {F : Set i → Set i} → (applicative₁ applicative₂ : Applicative F) → (∀{A : Set i} → pure applicative₁ {A} ＝ pure applicative₂ {A}) → (∀{A B : Set i} → ap applicative₁ {A} {B} ＝ ap applicative₂ {A} {B}) → applicative₁ ＝ applicative₂
Applicative-Eq
  applicative₁ applicative₂
  eq-pure
  eq-ap =
    Applicative-Eq-With-Body
      applicative₁
      applicative₂
      (to-Body-Eq-From-Applicative applicative₁ applicative₂ eq-pure eq-ap)
