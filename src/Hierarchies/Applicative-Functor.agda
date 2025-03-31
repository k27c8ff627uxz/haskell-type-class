{-# OPTIONS --prop #-}

module Hierarchies.Applicative-Functor where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Applicative-LiftA02

Applicative-to-Functor : {i : Level} → {F : Set i → Set i} → Applicative F → Functor F
Applicative-to-Functor
  {i} {F}
  record { pure = pure₀ ; ap = ap₀ ; Ap-Identity = Ap-Identity₀ ; Ap-Composition = Ap-Composition₀ ; Ap-Homomorphism = Ap-Homomorphism₀ ; Ap-Interchange = Ap-Interchange₀ }
  = record {
    fmap = fmap₀
    ; Fmap-Identity = \{A} →
      ＝-begin
        fmap₀ (id A)
      ＝⟨⟩
        ap₀ (pure₀ (id A))
      ＝⟨ Ap-Identity₀ ⟩
        id (F A)
      ＝-qed
    ; Fmap-Composition = \{A} {B} {C} → \{f : B → C} → \{g : A → B} → fun-ext _ _ (\α →
      ＝-begin
        fmap₀ (f ∘ g) α
      ＝⟨⟩
        ap₀ (pure₀ (f ∘ g)) α
      ＝⟨⟩
        ap₀ (pure₀ (_∘_ f g)) α
      ＝⟨- fun-eq (\x → ap₀ x α) (Ap-Homomorphism₀ _ _) ⟩
        ap₀ (ap₀ (pure₀ (_∘_ f)) (pure₀ g)) α
      ＝⟨- fun-eq (\x → ap₀ (ap₀ x (pure₀ g)) α) (Ap-Homomorphism₀ _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ f)) (pure₀ g)) α
      ＝⟨ Ap-Composition₀ _ _ _ ⟩
        ap₀ (pure₀ f) (ap₀ (pure₀ g) α)
      ＝⟨⟩
        fmap₀ f (fmap₀ g α)
      ＝⟨⟩
        (fmap₀ f ∘ fmap₀ g) α
      ＝-qed
    )
  }
  where
    fmap₀ : {A B : Set i} → (A → B) → F A → F B
    fmap₀ f = ap₀ (pure₀ f)
    
LiftA02-to-Functor : {i : Level} → {F : Set i → Set i} → LiftA02 F → Functor F
LiftA02-to-Functor {i} {F} lifta02 =
  record {
    fmap = liftA1₀
    ; Fmap-Identity = \{A} →
      ＝-begin
        liftA1₀ (id A)
      ＝⟨⟩
        liftA2₀ (id (A → A)) (liftA0₀ (id A))
      ＝⟨ LiftA2-Identity lifta02 ⟩
        id (F A)
      ＝-qed
    ; Fmap-Composition = \{A} {B} {C} → \{f : B → C} → \{g : A → B} → fun-ext _ _ (\(α : F A) →
      ＝-begin
        liftA1₀ (f ∘ g) α
      ＝⟨⟩
        liftA1₀ (\a → f (g a)) α
      ＝⟨- LiftA1-LiftA1-Composition lifta02 _ _ _ ⟩
        liftA1₀ f (liftA1₀ g α)
      ＝⟨⟩
        (liftA1₀ f ∘ liftA1₀ g) α
      ＝-qed
    )
      
  }
  where
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ = liftA2 lifta02
    liftA1₀ : {A B : Set i} → (A → B) → F A → F B
    liftA1₀ = liftA1 lifta02
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ = liftA0 lifta02

Applicative-to-Functor-fmap-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → {A B : Set i} → fmap (Applicative-to-Functor applicative) {A} {B} ＝ afmap applicative {A} {B}
Applicative-to-Functor-fmap-Eq {i} {F} applicative {A} {B} = ＝-refl _

LiftA02-to-Functor-fmap-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → {A B : Set i} → fmap (LiftA02-to-Functor lifta02) {A} {B} ＝ liftA1 lifta02 {A} {B}
LiftA02-to-Functor-fmap-Eq {i} {F} lifta02 {A} {B} = ＝-refl _

LiftA02-Applicative-Functor-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → Applicative-to-Functor (LiftA02-to-Applicative lifta02) ＝ LiftA02-to-Functor lifta02
LiftA02-Applicative-Functor-Eq {i} {F} lifta02 =
  let applicative : Applicative F
      applicative = LiftA02-to-Applicative lifta02
  in Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\(f : A → B) →
      ＝-begin
        fmap (Applicative-to-Functor (LiftA02-to-Applicative lifta02)) f
      ＝⟨⟩
        fmap (Applicative-to-Functor applicative) f
      ＝⟨⟩
        (ap applicative) (pure applicative f)
      ＝⟨⟩
        liftA1 (lifta02) f
      ＝⟨⟩
        fmap (LiftA02-to-Functor lifta02) f
      ＝-qed
    ))

Applicative-LiftA02-Functor-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → LiftA02-to-Functor (Applicative-to-LiftA02 applicative) ＝ Applicative-to-Functor applicative
Applicative-LiftA02-Functor-Eq {i} {F} applicative =
  let lifta02 : LiftA02 F
      lifta02 = Applicative-to-LiftA02 applicative
  in Functor-Equal
    _
    _
    (\A B →
      ＝-begin
        fmap (LiftA02-to-Functor (Applicative-to-LiftA02 applicative))
      ＝⟨⟩
        liftA1 (Applicative-to-LiftA02 applicative)
      ＝⟨- AFmap-Eq-LiftA1 applicative ⟩
        afmap applicative
      ＝⟨⟩
        fmap (Applicative-to-Functor applicative)
      ＝-qed
    )
