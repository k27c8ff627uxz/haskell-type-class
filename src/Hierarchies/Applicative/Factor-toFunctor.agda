{-# OPTIONS --prop #-}

module Hierarchies.Applicative.Factor-toFunctor where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Applicative.toFunctor
open import Hierarchies.Applicative.Translates

Applicative-to-LiftA02-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → LiftA02-to-Functor (Applicative-to-LiftA02 applicative) ＝ Applicative-to-Functor applicative
Applicative-to-LiftA02-to-Functor-Eq {i} {F} applicative =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\f → fun-ext _ _ (\α →
      ＝-begin
        fmap (LiftA02-to-Functor lifta02) f α
      ＝⟨⟩
        liftA1 lifta02 f α
      ＝⟨⟩
        liftA2 lifta02 (id (A → B)) (liftA0 lifta02 f) α
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (id (A → B))) (pure₀ f)) α
      ＝⟨ fun-eq (\x → ap₀ x α) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (pure₀ ((id (A → B)) f)) α
      ＝⟨⟩
        ap₀ (pure₀ f) α
      ＝⟨⟩
        fmap (Applicative-to-Functor applicative) f α
      ＝-qed
    ))) where
      pure₀ : ∀{A} → A → F A
      pure₀ = pure applicative
      ap₀ : ∀{A B : Set i} → F (A → B) → F A → F B
      ap₀ = ap applicative
      lifta02 : LiftA02 F
      lifta02 = Applicative-to-LiftA02 applicative

Applicative-to-LiftA02-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → LiftA02-to-FunctorWithUnit (Applicative-to-LiftA02 applicative) ＝ Applicative-to-FunctorWithUnit applicative
Applicative-to-LiftA02-to-FunctorWithUnit-Eq {i} {F} applicative =
  FunctorWithUnit-Eq
    _
    _
    (Applicative-to-LiftA02-to-Functor-Eq applicative)
    (\{A} → ＝-refl _)


Applicative-to-ProductiveFunctor-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → ProductiveFunctor-to-Functor (Applicative-to-ProductiveFunctor applicative) ＝ Applicative-to-Functor applicative
Applicative-to-ProductiveFunctor-to-Functor-Eq {i} {F} applicative = ＝-refl _

Applicative-to-ProductiveFunctor-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → ProductiveFunctor-to-FunctorWithUnit (Applicative-to-ProductiveFunctor applicative) ＝ Applicative-to-FunctorWithUnit applicative
Applicative-to-ProductiveFunctor-to-FunctorWithUnit-Eq applicative = ＝-refl _


LiftA02-to-Applicative-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → Applicative-to-Functor (LiftA02-to-Applicative lifta02) ＝ LiftA02-to-Functor lifta02
LiftA02-to-Applicative-to-Functor-Eq {i} {F} lifta02 =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\f → fun-ext _ _ (\α →
      ＝-begin
        fmap (Applicative-to-Functor applicative) f α
      ＝⟨⟩
        ap applicative (pure applicative f) α
      ＝⟨⟩
        liftA2₀ (id (A → B)) (liftA0₀ f) α
      ＝⟨⟩
        liftA1 lifta02 f α
      ＝⟨⟩
        fmap (LiftA02-to-Functor lifta02) f α
      ＝-qed
    )))
    where
      liftA0₀ : {A : Set i} → A → F A
      liftA0₀ = liftA0 lifta02
      liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
      liftA2₀ = liftA2 lifta02
      applicative : Applicative F
      applicative = LiftA02-to-Applicative lifta02

LiftA02-to-Applicative-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → Applicative-to-FunctorWithUnit (LiftA02-to-Applicative lifta02) ＝ LiftA02-to-FunctorWithUnit lifta02
LiftA02-to-Applicative-to-FunctorWithUnit-Eq {i} {F} lifta02 =
  FunctorWithUnit-Eq
    _
    _
    (LiftA02-to-Applicative-to-Functor-Eq lifta02)
    (\{A} → ＝-refl _)


LiftA02-to-ProductiveFunctor-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → ProductiveFunctor-to-Functor (LiftA02-to-ProductiveFunctor lifta02) ＝ LiftA02-to-Functor lifta02
LiftA02-to-ProductiveFunctor-to-Functor-Eq {i} {F} lifta02 = ＝-refl _

LiftA02-to-ProductiveFunctor-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor lifta02) ＝ LiftA02-to-FunctorWithUnit lifta02
LiftA02-to-ProductiveFunctor-to-FunctorWithUnit-Eq lifta02 = ＝-refl _


ProductiveFunctor-to-Applicative-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → Applicative-to-Functor (ProductiveFunctor-to-Applicative pfunctor) ＝ ProductiveFunctor-to-Functor pfunctor
ProductiveFunctor-to-Applicative-to-Functor-Eq {i} {F} pfunctor =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\f → fun-ext _ _ (\α →
      ＝-begin
        fmap (Applicative-to-Functor applicative) f α
      ＝⟨⟩
        ap applicative (pure applicative f) α
      ＝⟨⟩
        pfmap₀ pMapApply (fpair₀ (punit₀ f) α)
      ＝⟨ fun-eq (\x → pfmap₀ pMapApply x) (Fpair-Homomorphism1 pfunctor _ _) ⟩
        pfmap₀ pMapApply (pfmap₀ (\a → (f , a)) α)
      ＝⟨- PFmap-Composition' pfunctor α ⟩
        pfmap₀ (pMapApply ∘ (\a → (f , a))) α
      ＝⟨⟩
        pfmap₀ (\a → f a) α
      ＝⟨⟩
        pfmap₀ f α
      ＝⟨⟩
        fmap (ProductiveFunctor-to-Functor pfunctor) f α
      ＝-qed
    ))) where
      applicative : Applicative F
      applicative = ProductiveFunctor-to-Applicative pfunctor
      pfmap₀ : {A B : Set i} → (A → B) → F A → F B
      pfmap₀ = pfmap pfunctor
      punit₀ : {A : Set i} → A → F A
      punit₀ = punit pfunctor
      fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
      fpair₀ = fpair pfunctor

ProductiveFunctor-to-Applicative-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → Applicative-to-FunctorWithUnit (ProductiveFunctor-to-Applicative pfunctor) ＝ ProductiveFunctor-to-FunctorWithUnit pfunctor
ProductiveFunctor-to-Applicative-to-FunctorWithUnit-Eq {i} {F} pfunctor =
  FunctorWithUnit-Eq
    _
    _
    (ProductiveFunctor-to-Applicative-to-Functor-Eq pfunctor)
    (＝-refl _)

ProductiveFunctor-to-LiftA02-to-Functor-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → LiftA02-to-Functor (ProductiveFunctor-to-LiftA02 pfunctor) ＝ ProductiveFunctor-to-Functor pfunctor
ProductiveFunctor-to-LiftA02-to-Functor-Eq {i} {F} pfunctor =
  Functor-Equal
    _
    _
    (\A B → fun-ext _ _ (\f → fun-ext _ _ (\α →
      ＝-begin
        fmap (LiftA02-to-Functor lifta02) f α
      ＝⟨⟩
        liftA1 lifta02 f α
      ＝⟨⟩
        liftA2 lifta02 (id (A → B)) (liftA0 lifta02 f) α
      ＝⟨⟩
        pfmap₀ (\p → (id (A → B)) (fst p) (snd p)) (fpair₀ (punit₀ f) α)
      ＝⟨⟩
        pfmap₀ (\p → (fst p) (snd p)) (fpair₀ (punit₀ f) α)
      ＝⟨ fun-eq (\x → pfmap₀ (\p → fst p (snd p)) x) (Fpair-Homomorphism1 pfunctor f α) ⟩
        pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\a → (f , a)) α)
      ＝⟨- PFmap-Composition' pfunctor α ⟩
        pfmap₀ ((\p → (fst p) (snd p)) ∘ (\a → (f , a))) α
      ＝⟨⟩
        pfmap₀ (\a → (fst (f , a)) (snd (f , a))) α
      ＝⟨⟩
        pfmap₀ (\a → f a) α
      ＝⟨⟩
        pfmap₀ f α
      ＝⟨⟩
        fmap (ProductiveFunctor-to-Functor pfunctor) f α
      ＝-qed
    ))) where
      lifta02 : LiftA02 F
      lifta02 = ProductiveFunctor-to-LiftA02 pfunctor
      punit₀ : {A : Set i} → A → F A
      punit₀ = punit pfunctor
      pfmap₀ : {A B : Set i} → (A → B) → F A → F B
      pfmap₀ = pfmap pfunctor
      fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
      fpair₀ = fpair pfunctor

ProductiveFunctor-to-LiftA02-to-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → LiftA02-to-FunctorWithUnit (ProductiveFunctor-to-LiftA02 pfunctor) ＝ ProductiveFunctor-to-FunctorWithUnit pfunctor
ProductiveFunctor-to-LiftA02-to-FunctorWithUnit-Eq {i} {F} pfunctor =
  FunctorWithUnit-Eq
    _
    _
    (ProductiveFunctor-to-LiftA02-to-Functor-Eq pfunctor)
    (\{A} → ＝-refl _)
