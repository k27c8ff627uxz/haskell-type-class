{-# OPTIONS --prop #-}

module Facts.Translate.Applicative-FunctorWithUnit where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Facts.Translate.Applicative-LiftA02
open import Facts.Translate.Applicative-Functor

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
      ＝⟨ fun-eq (\x → x f (liftA0₀ a)) (LiftA02-to-Functor-fmap-Eq lifta02) ⟩
        liftA1₀ f (liftA0₀ a)
      ＝⟨ LiftA1-Homomorphism lifta02 f a ⟩
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

Applicative-to-FunctorWithUnit-unit-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → {A : Set i} → unit (Applicative-to-FunctorWithUnit applicative) {A} ＝ pure applicative {A}
Applicative-to-FunctorWithUnit-unit-Eq {i} {F} applicative {A} = ＝-refl _

LiftA02-to-FunctorWithUnit-unit-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → {A : Set i} → unit (LiftA02-to-FunctorWithUnit lifta02) {A} ＝ liftA0 lifta02
LiftA02-to-FunctorWithUnit-unit-Eq {i} {F} lifta02 {A} = ＝-refl _

LiftA02-to-FunctorWithUnit-ufmap-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → {A B : Set i} → ufmap (LiftA02-to-FunctorWithUnit lifta02) {A} {B} ＝ fmap (LiftA02-to-Functor lifta02) {A} {B}
LiftA02-to-FunctorWithUnit-ufmap-Eq {i} {F} lifta02 {A} {B} = ＝-refl _

LiftA02-Applicative-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → Applicative-to-FunctorWithUnit (LiftA02-to-Applicative lifta02) ＝ LiftA02-to-FunctorWithUnit lifta02
LiftA02-Applicative-FunctorWithUnit-Eq {i} {F} lifta02 =
  FunctorWithUnit-Eq
    _ _
    (
      ＝-begin
        FunctorWithUnit-to-Functor (Applicative-to-FunctorWithUnit (LiftA02-to-Applicative lifta02))
      ＝⟨⟩
        Applicative-to-Functor (LiftA02-to-Applicative lifta02)
      ＝⟨ LiftA02-Applicative-Functor-Eq lifta02 ⟩
        LiftA02-to-Functor lifta02
      ＝⟨⟩
        FunctorWithUnit-to-Functor (LiftA02-to-FunctorWithUnit lifta02)
      ＝-qed
    )
    (\{A} →
      ＝-begin
        unit (Applicative-to-FunctorWithUnit (LiftA02-to-Applicative lifta02))
      ＝⟨⟩
        pure (LiftA02-to-Applicative lifta02)
      ＝⟨⟩
        liftA0 lifta02
      ＝⟨⟩
        unit (LiftA02-to-FunctorWithUnit lifta02)
      ＝-qed
    )

Applicative-LiftA02-FunctorWithUnit-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → LiftA02-to-FunctorWithUnit (Applicative-to-LiftA02 applicative) ＝ Applicative-to-FunctorWithUnit applicative
Applicative-LiftA02-FunctorWithUnit-Eq {i} {F} applicative =
  FunctorWithUnit-Eq
    _ _
    (
      ＝-begin
        FunctorWithUnit-to-Functor (LiftA02-to-FunctorWithUnit (Applicative-to-LiftA02 applicative))
      ＝⟨⟩
        LiftA02-to-Functor (Applicative-to-LiftA02 applicative)
      ＝⟨ Applicative-LiftA02-Functor-Eq applicative ⟩
        Applicative-to-Functor applicative
      ＝⟨⟩
        FunctorWithUnit-to-Functor (Applicative-to-FunctorWithUnit applicative)
      ＝-qed
    )
    (\{A} →
      ＝-begin
        unit (LiftA02-to-FunctorWithUnit (Applicative-to-LiftA02 applicative))
      ＝⟨⟩
        liftA0 (Applicative-to-LiftA02 applicative)
      ＝⟨⟩
        pure applicative
      ＝⟨⟩
        unit (Applicative-to-FunctorWithUnit applicative)
      ＝-qed
    )
