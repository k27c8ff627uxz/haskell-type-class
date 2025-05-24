{-# OPTIONS --prop #-}

module Hierarchies.Applicative.toFunctor where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs

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

ProductiveFunctor-to-Functor : {i : Level} → {F : Set i → Set i} → ProductiveFunctor F → Functor F
ProductiveFunctor-to-Functor {i} {F} pfunctor = FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit pfunctor)


Applicative-to-FunctorWithUnit : {i : Level} → {F : Set i → Set i} → Applicative F → FunctorWithUnit F
Applicative-to-FunctorWithUnit {i} {F} applicative
  = record {
    FunctorWithUnit-to-Functor = FunctorWithUnit-to-Functor₀
    ; unit = unit₀
    ; Unit-Homomorphism = \{A} {B} → \(a : A) → \(f : A → B) →
      ＝-begin
        ufmap₀ f (unit₀ a)
      ＝⟨⟩
        ap₀ (pure₀ f) (pure₀ a)
      ＝⟨ Ap-Homomorphism applicative f a ⟩
        pure₀ (f a)
      ＝⟨⟩
        unit₀ (f a)
      ＝-qed
  }
  where
    ap₀ : {A B : Set i} → F (A → B) → F A → F B
    ap₀ = ap applicative
    pure₀ : {A : Set i} → A → F A
    pure₀ = pure applicative
    unit₀ : {A : Set i} → A → F A
    unit₀ = pure₀
    FunctorWithUnit-to-Functor₀ : Functor F
    FunctorWithUnit-to-Functor₀ = Applicative-to-Functor applicative
    ufmap₀ : {A B : Set i} → (A → B) → F A → F B
    ufmap₀ = fmap FunctorWithUnit-to-Functor₀

LiftA02-to-FunctorWithUnit : {i : Level} → {F : Set i → Set i} → LiftA02 F → FunctorWithUnit F
LiftA02-to-FunctorWithUnit {i} {F} lifta02
  = record {
    FunctorWithUnit-to-Functor = FunctorWithUnit-to-Functor₀
    ; unit = liftA0₀
    ; Unit-Homomorphism = \{A} {B} → \(a : A) → \(f : A → B) →
      ＝-begin
        fmap FunctorWithUnit-to-Functor₀ f (liftA0₀ a)
      ＝⟨⟩
        fmap (LiftA02-to-Functor lifta02) f (liftA0₀ a)
      ＝⟨⟩
        liftA1₀ f (liftA0₀ a)
      ＝⟨⟩
        liftA2₀ (id (A → B)) (liftA0₀ f) (liftA0₀ a)
      ＝⟨ LiftA2-Homomorphism lifta02 _ _ _ ⟩
        liftA0₀ ((id (A → B)) f a)
      ＝⟨⟩
        liftA0₀ (f a)
      ＝-qed
  }
  where
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ = liftA0 lifta02
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ = liftA2 lifta02
    liftA1₀ : {A B : Set i} → (A → B) → F A → F B
    liftA1₀ = liftA1 lifta02
    FunctorWithUnit-to-Functor₀ : Functor F
    FunctorWithUnit-to-Functor₀ = LiftA02-to-Functor lifta02
