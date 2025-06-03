{-# OPTIONS --prop #-}

module Instances.Maybe.Classes where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Instances.Maybe.Def

Maybe-Functor : {i : Level} → Functor {i} Maybe
Maybe-Functor {i} =
  record {
    fmap = fmap₀
    ; Fmap-Identity = \{A} → fun-ext _ _ \{ Nothing → ＝-refl _ ; (Just a) → ＝-refl _ }
    ; Fmap-Composition = \{A B C} → \{f : B → C} → \{g : A → B} → fun-ext _ _ \{ Nothing → ＝-refl _ ; (Just a) → ＝-refl _ }
  } where
    fmap₀ : {A B : Set i} → (A → B) → Maybe A → Maybe B
    fmap₀ {A} {B} f Nothing = Nothing
    fmap₀ {A} {B} f (Just a) = Just (f a)

Maybe-FunctorWithUnit : {i : Level} → FunctorWithUnit {i} Maybe
Maybe-FunctorWithUnit {i} =
  record {
    FunctorWithUnit-to-Functor = Maybe-Functor {i}
    ; unit = \{A} → Just
    ; Unit-Homomorphism = \{A B} → \(a : A) → \(f : A → B) →
      ＝-begin
        fmap Maybe-Functor f (Just a)
      ＝⟨⟩
        Just (f a)
      ＝-qed
  }

Maybe-Applicative : {i : Level} → Applicative {i} Maybe
Maybe-Applicative {i} =
  record {
    pure = pure₀
    ; ap = ap₀
    ; Ap-Identity = \{A} → fun-ext _ _ \{
        Nothing →
          ＝-begin
            ap₀ (pure₀ (id A)) Nothing
          ＝⟨⟩
            id (Maybe A) Nothing
          ＝-qed
        ; (Just a) →
          ＝-begin
            ap₀ (pure₀ (id A)) (Just a)
          ＝⟨⟩
            id (Maybe A) (Just a)
          ＝-qed
        }
    ; Ap-Composition = \{A B C} → \{
        Nothing → \v → \w → ＝-refl _
        ; (Just g) → \{
          Nothing → \w → ＝-refl _
          ; (Just f) → \{
            Nothing → ＝-refl _
            ; (Just a) → ＝-refl _
          }
        }
      }
    ; Ap-Interchange = \{A B} → \{
        Nothing → \y → ＝-refl _
        ; (Just f) → \y → ＝-refl _
      }
    ; Ap-Homomorphism = \{A} {B} → \(f : A → B) → \(a : A) → ＝-refl _
  } where
      pure₀ : {A : Set i} → A → Maybe A
      pure₀ = Just
      ap₀ : {A B : Set i} → Maybe (A → B) → Maybe A → Maybe B
      ap₀ Nothing _ = Nothing
      ap₀ (Just f) Nothing = Nothing
      ap₀ (Just f) (Just a) = Just (f a)

Maybe-LiftA02 : {i : Level} → LiftA02 {i} Maybe
Maybe-LiftA02 {i} =
  record {
    liftA0 = liftA0₀
    ; liftA2 = liftA2₀
    ; LiftA2-Identity = \{A} → fun-ext _ _ \{
        Nothing → ＝-refl _
        ; (Just a) → ＝-refl _
      }
    ; LiftA2-Homomorphism = \{A B C} → \f → \a → \b → ＝-refl _
    ; LiftA2-Homomorphism2 = \{A B C} → \f → \{
        Nothing → \b → ＝-refl _
        ; (Just a) → \b → ＝-refl _
      }
    ; LiftA2-LiftA1-Composition1 = \{A A' B C} → \f → \g → \{
        Nothing → \β → ＝-refl _
        ; (Just a) → \{
          Nothing → ＝-refl _
          ; (Just b) → ＝-refl _
        }
      }
    ; LiftA2-LiftA2-Composition1 = \{A B C D E} → \f → \g → \{
        Nothing → \β → \δ → ＝-refl _
        ; (Just a) → \{
          Nothing → \δ → ＝-refl _
          ; (Just b) → \{
            Nothing → ＝-refl _
            ; (Just d) → ＝-refl _
          }
        }
      }
    ; LiftA2-LiftA2-Composition2 =  \{A B C D E} → \f → \g → \{
        Nothing → \β → \{
          Nothing → ＝-refl _
          ; (Just c) → ＝-refl _
        }
        ; (Just a) → \{
          Nothing → \{
            Nothing → ＝-refl _
            ; (Just c) → ＝-refl _
          }
          ; (Just b) → \{
            Nothing → ＝-refl _
            ; (Just c) → ＝-refl _
          }
        }
      }
  } where
      liftA0₀ : {A : Set i} → A → Maybe A
      liftA0₀ = Just
      liftA2₀ : {A B C : Set i} → (A → B → C) → Maybe A → Maybe B → Maybe C
      liftA2₀ f Nothing _ = Nothing
      liftA2₀ f (Just a) Nothing = Nothing
      liftA2₀ f (Just a) (Just b) = Just (f a b)

Maybe-ProductiveFunctor : {i : Level} → ProductiveFunctor {i} Maybe
Maybe-ProductiveFunctor {i} =
  record {
    ProductiveFunctor-to-FunctorWithUnit = Maybe-FunctorWithUnit
    ; fpair = fpair₀
    ; Fpair-Homomorphism1 = \{A B} → \(a : A) → \{
        Nothing → ＝-refl _
        ; (Just b) → ＝-refl _
      }
    ; Fpair-Homomorphism2 = \{A B} → \{
        Nothing → \b → ＝-refl _
        ; (Just a) → \b → ＝-refl _
      }
    ; Fpair-Associative = \{A B C} → \{
        Nothing → \β → \γ → ＝-refl _
        ; (Just a) → \{
          Nothing → \γ → ＝-refl _
          ; (Just b) → \{
            Nothing → ＝-refl _
            ; (Just c) → ＝-refl _
          }
        }
      }
    ; Fpair-Fmap-Composition = \{A A' B B'} → \f → \g → \{
        Nothing → \β → ＝-refl _
        ; (Just a) → \{
            Nothing → ＝-refl _
            ; (Just b) → ＝-refl _
        }
      }
  } where
    fpair₀ : {A B : Set i} → Maybe A → Maybe B → Maybe (Pair A B)
    fpair₀ Nothing _ = Nothing
    fpair₀ (Just a) Nothing = Nothing
    fpair₀ (Just a) (Just b) = Just (a , b)

Maybe-Monad : {i : Level} → Monad {i} Maybe
Maybe-Monad {i} =
  record {
    return = return₀
    ; bind = bind₀
    ; Return-Left-Identity = \{A B} → \(f : A → Maybe B) → \(a : A) → ＝-refl _
    ; Return-Right-Identity = \{A} → \{ Nothing → ＝-refl _ ; (Just a) → ＝-refl _ }
    ; Bind-Composition = \{A B C} → \(f : A → Maybe B) → \(g : B → Maybe C) → \{ Nothing → ＝-refl _ ; (Just a) → ＝-refl _}
  } where
    return₀ : {A : Set i} → A → Maybe A
    return₀ = Just
    bind₀ : {A B : Set i} → Maybe A → (A → Maybe B) → Maybe B
    bind₀ Nothing f = Nothing
    bind₀ (Just a) f = f a

