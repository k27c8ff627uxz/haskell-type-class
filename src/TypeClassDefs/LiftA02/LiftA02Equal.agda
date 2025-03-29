{-# OPTIONS --prop #-}

module TypeClassDefs.LiftA02.LiftA02Equal where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.LiftA02.Def

private
  record Body {i} (F : Set i → Set i) : Set (lsuc i) where
    field
      liftA0 : {A : Set i} → A → F A
      liftA2 : {A B C : Set i} → (A → B → C) → F A → F B → F C

  Body-Explicit : {i : Level} → {F : Set i → Set i} → ((A : Set i) → A → F A) → ((A B C : Set i) → (A → B → C) → F A → F B → F C) → Body F
  Body-Explicit liftA0₀ liftA2₀ = record { liftA0 = \{A} → liftA0₀ A ; liftA2 = \{A B C} → liftA2₀ A B C }

  Body-Explicit-Eq : {i : Level} → {F : Set i → Set i} → (liftA0₁ liftA0₂ : (A : Set i) → A → F A) → (liftA2₁ liftA2₂ : (A B C : Set i) → (A → B → C) → F A → F B → F C) → liftA0₁ ＝ liftA0₂ → liftA2₁ ＝ liftA2₂ → Body-Explicit liftA0₁ liftA2₁ ＝ Body-Explicit liftA0₂ liftA2₂
  Body-Explicit-Eq liftA0₀ liftA0₀ liftA2₀ liftA2₀ (＝-refl liftA0₁) (＝-refl liftA2₀) = ＝-refl (Body-Explicit liftA0₀ liftA2₀)

  to-Body : {i : Level} → {F : Set i → Set i} → (liftA02 : LiftA02 F) → Body F
  to-Body record { liftA0 = liftA0₀ ; liftA2 = liftA2₀ } = record { liftA0 = liftA0₀ ; liftA2 = liftA2₀ }

  to-Body-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → ({A : Set i} → Body.liftA0 body₁ {A} ＝ Body.liftA0 body₂ {A}) → ({A B C : Set i} → Body.liftA2 body₁ {A} {B} {C} ＝ Body.liftA2 body₂ {A} {B} {C}) → body₁ ＝ body₂
  to-Body-Eq
    {i} {F}
    record { liftA0 = liftA0₁ ; liftA2 = liftA2₁ }
    record { liftA0 = liftA0₂ ; liftA2 = liftA2₂ }
    eq-liftA0 eq-liftA2
    = ＝-begin
      record { liftA0 = liftA0₁ ; liftA2 = liftA2₁ }
    ＝⟨ ＝-refl _ ⟩
      Body-Explicit (\A → liftA0₁ {A}) (\(A B C : Set i) → liftA2₁ {A} {B} {C})
    ＝⟨
        Body-Explicit-Eq _ _ _ _ (fun-ext-dep _ _ (\A → eq-liftA0 {A})) (fun-ext-dep _ _ (\A → fun-ext-dep _ _ (\B → fun-ext-dep _ _ (\C → eq-liftA2 {A} {B} {C}))))
      ⟩
      Body-Explicit (\A → liftA0₂ {A}) (\(A B C : Set i) → liftA2₂ {A} {B} {C})
    ＝⟨ ＝-refl _ ⟩
      record { liftA0 = liftA0₂ ; liftA2 = liftA2₂ }
    ＝-qed
  
  record Conditions {i} {F : Set i → Set i} (body : Body F) : Prop (lsuc i) where
    liftA0' : {A : Set i} → A → F A
    liftA0' = Body.liftA0 body
    liftA2' : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2' = Body.liftA2 body
    liftA1' : {A B : Set i} → (A → B) → F A → F B
    liftA1' {A} {B} f fa = liftA2' (id (A → B)) (liftA0' f) fa
    liftA3' : {A B C D : Set i} → (A → B → C → D) → F A → F B → F C → F D
    liftA3' {A} {B} {C} {D} f α β γ = liftA2' (id (C → D)) (liftA2' f α β) γ

    field
      LiftA2-Identity : {A : Set i} → liftA2' (id (A → A)) (liftA0' (id A)) ＝ id (F A)
      LiftA2-Homomorphism : {A B C : Set i} → (f : A → B → C) → (a : A) → (b : B) → liftA2' f (liftA0' a) (liftA0' b) ＝ liftA0' (f a b)
      LiftA2-Homomorphism2 : {A B C : Set i} → (f : A → B → C) → (α : F A) → (b : B) → liftA2' f α (liftA0' b) ＝ liftA1' (\a → f a b) α
      LiftA2-LiftA1-Composition1 : {A A' B C : Set i} → (f : A' → B → C) → (g : A → A') → (α : F A) → (β : F B) → liftA2' f (liftA1' g α) β ＝ liftA2' (\a → \b → f (g a) b) α β
      LiftA2-LiftA2-Composition1 : {A B C D E : Set i} → (f : C → D → E) → (g : A → B → C) → (α : F A) → (β : F B) → (δ : F D) → liftA2' f (liftA2' g α β) δ ＝ liftA3' (\a → \b → \d → f (g a b) d) α β δ
      LiftA2-LiftA2-Composition2 : {A B C D E : Set i} → (f : C → D → E) → (g : A → B → D) → (α : F A) → (β : F B) → (γ : F C) → liftA2' f γ (liftA2' g α β) ＝ liftA3' (\c → \a → \b → f c (g a b)) γ α β

  to-Condition : {i : Level} → {F : Set i → Set i} → (liftA02 : LiftA02 F) → Conditions (to-Body liftA02)
  to-Condition
    record { liftA0 = liftA0₀ ; liftA2 = liftA2₀ ; LiftA2-Identity = LiftA2-Identity₀ ; LiftA2-Homomorphism = LiftA2-Homomorphism₀ ; LiftA2-Homomorphism2 = LiftA2-Homomorphism2₀ ; LiftA2-LiftA1-Composition1 = LiftA2-LiftA1-Composition1₀ ; LiftA2-LiftA2-Composition1 = LiftA2-LiftA2-Composition1₀ ; LiftA2-LiftA2-Composition2 = LiftA2-LiftA2-Composition2₀ }
    = record { LiftA2-Identity = LiftA2-Identity₀ ; LiftA2-Homomorphism = LiftA2-Homomorphism₀ ; LiftA2-Homomorphism2 = LiftA2-Homomorphism2₀ ; LiftA2-LiftA1-Composition1 = LiftA2-LiftA1-Composition1₀ ; LiftA2-LiftA2-Composition1 = LiftA2-LiftA2-Composition1₀ ; LiftA2-LiftA2-Composition2 = LiftA2-LiftA2-Composition2₀ }
    
  to-LiftA02 : {i : Level} → {F : Set i → Set i} → (body : Body F) → (conditions : Conditions body) → LiftA02 F
  to-LiftA02
    record { liftA0 = liftA0₀ ; liftA2 = liftA2₀ }
    record { LiftA2-Identity = LiftA2-Identity₀ ; LiftA2-Homomorphism = LiftA2-Homomorphism₀ ; LiftA2-Homomorphism2 = LiftA2-Homomorphism2₀ ; LiftA2-LiftA1-Composition1 = LiftA2-LiftA1-Composition1₀ ; LiftA2-LiftA2-Composition1 = LiftA2-LiftA2-Composition1₀ ; LiftA2-LiftA2-Composition2 = LiftA2-LiftA2-Composition2₀ }
    = record { liftA0 = liftA0₀ ; liftA2 = liftA2₀ ; LiftA2-Identity = LiftA2-Identity₀ ; LiftA2-Homomorphism = LiftA2-Homomorphism₀ ; LiftA2-Homomorphism2 = LiftA2-Homomorphism2₀ ; LiftA2-LiftA1-Composition1 = LiftA2-LiftA1-Composition1₀ ; LiftA2-LiftA2-Composition1 = LiftA2-LiftA2-Composition1₀ ; LiftA2-LiftA2-Composition2 = LiftA2-LiftA2-Composition2₀ }
    
  LiftA02-to-LiftA02-Eq : {i : Level} → {F : Set i → Set i} → (liftA02 : LiftA02 F) → liftA02 ＝ to-LiftA02 (to-Body liftA02) (to-Condition liftA02)
  LiftA02-to-LiftA02-Eq liftA02 = ＝-refl _

  to-LiftA02-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (conditions₁ : Conditions body₁) → (conditions₂ : Conditions body₂) → body₁ ＝ body₂ → to-LiftA02 body₁ conditions₁ ＝ to-LiftA02 body₂ conditions₂
  to-LiftA02-Eq
    body₁ body₂ conditions₁ conditions₂ eq-body
    = proof-irrelevance-with-type _ _ _ to-LiftA02 body₁ body₂ conditions₁ conditions₂ eq-body

  LiftA02-Eq-With-Body : {i : Level} → {F : Set i → Set i} → (liftA02₁ liftA02₂ : LiftA02 F) → (to-Body liftA02₁ ＝ to-Body liftA02₂) → liftA02₁ ＝ liftA02₂
  LiftA02-Eq-With-Body liftA02₁ liftA02₂ eq-body =
    ＝-begin
      liftA02₁
    ＝⟨ LiftA02-to-LiftA02-Eq liftA02₁ ⟩
      to-LiftA02 (to-Body liftA02₁) (to-Condition liftA02₁)
    ＝⟨ to-LiftA02-Eq (to-Body liftA02₁) (to-Body liftA02₂) (to-Condition liftA02₁) (to-Condition liftA02₂) eq-body ⟩
      to-LiftA02 (to-Body liftA02₂) (to-Condition liftA02₂)
    ＝⟨- LiftA02-to-LiftA02-Eq liftA02₂ ⟩
      liftA02₂
    ＝-qed


LiftA02-Eq : {i : Level} → {F : Set i → Set i} → (liftA02₁ liftA02₂ : LiftA02 F) → ({A : Set i} → liftA0 liftA02₁ {A} ＝ liftA0 liftA02₂ {A}) → ({A B C : Set i} → liftA2 liftA02₁ {A} {B} {C} ＝ liftA2 liftA02₂ {A} {B} {C}) → liftA02₁ ＝ liftA02₂
LiftA02-Eq
  liftA02₁ liftA02₂ eq-liftA0 eq-liftA2
  = LiftA02-Eq-With-Body liftA02₁ liftA02₂ (to-Body-Eq _ _ eq-liftA0 eq-liftA2)
