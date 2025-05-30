{-# OPTIONS --prop #-}

module Hierarchies.Monad.Factor-Translates where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Applicative
open import Hierarchies.Monad.Translates
open import Hierarchies.Monad.Factor-toFunctor

Monad-to-Applicative-to-LiftA02-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → Applicative-to-LiftA02 (Monad-to-Applicative monad) ＝ Monad-to-LiftA02 monad
Monad-to-Applicative-to-LiftA02-Eq {i} {F} monad =
  LiftA02-Eq
    _
    _
    (\{A} →
      ＝-begin
        liftA0 (Applicative-to-LiftA02 (Monad-to-Applicative monad))
      ＝⟨⟩
        pure (Monad-to-Applicative monad)
      ＝⟨⟩
        return₀
      ＝⟨⟩
        liftA0 (Monad-to-LiftA02 monad)
      ＝-qed
    )
    (\{A B C} → fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\α → fun-ext _ _ (\β →
      ＝-begin
        liftA2 (Applicative-to-LiftA02 applicative) f α β
      ＝⟨⟩
        ap applicative (ap applicative (pure applicative f) α) β
      ＝⟨⟩
        bind₀ (bind₀ (return₀ f) (\r → bind₀ α (\a → return₀ (r a)))) (\s → bind₀ β (\b → return₀ (s b)))
      ＝⟨ fun-eq (\x → bind₀ x (\s → bind₀ β (\b → return₀ (s b)))) (Return-Left-Identity monad _ _) ⟩
        bind₀ ((\r → bind₀ α (\a → return₀ (r a))) f) (\s → bind₀ β (\b → return₀ (s b)))
      ＝⟨⟩
        bind₀ (bind₀ α (\a → return₀ (f a))) (\s → bind₀ β (\b → return₀ (s b)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (return₀ (f a)) (\s → bind₀ β (\b → return₀ (s b))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → (\s → bind₀ β (\b → return₀ (s b))) (f a))
      ＝⟨⟩
        bind₀ α (\a → bind₀ β (\b → return₀ (f a b)))
      ＝⟨⟩
        liftA2 (Monad-to-LiftA02 monad) f α β
      ＝-qed
    ))))
  where
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    applicative : Applicative F
    applicative = Monad-to-Applicative monad


Monad-to-Applicative-to-ProductiveFunctor-Eq : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → Applicative-to-ProductiveFunctor (Monad-to-Applicative monad) ＝ Monad-to-ProductiveFunctor monad
Monad-to-Applicative-to-ProductiveFunctor-Eq {i} {F} monad =
  ProductiveFunctor-Eq
    _
    _
    (
      ＝-begin
        ProductiveFunctor-to-FunctorWithUnit (Applicative-to-ProductiveFunctor (Monad-to-Applicative monad))
      ＝⟨ Applicative-to-ProductiveFunctor-to-FunctorWithUnit-Eq (Monad-to-Applicative monad) ⟩
        Applicative-to-FunctorWithUnit (Monad-to-Applicative monad)
      ＝⟨ Monad-to-Applicative-to-FunctorWithUnit-Eq monad ⟩
        Monad-to-FunctorWithUnit monad
      ＝⟨- Monad-to-ProductiveFunctor-to-FunctorWithUnit-Eq monad ⟩
        ProductiveFunctor-to-FunctorWithUnit (Monad-to-ProductiveFunctor monad)
      ＝-qed
    )
    (\A B → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        fpair (Applicative-to-ProductiveFunctor applicative) α β
      ＝⟨⟩
        ap applicative (ap applicative (pure applicative createPair) α) β
      ＝⟨⟩
        bind₀ (bind₀ (return₀ createPair) (\f → bind₀ α (\a → return₀ (f a)))) (\f → bind₀ β (\b → return₀ (f b)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ (return₀ createPair) (\r → bind₀ ((\f → bind₀ α (\a → return₀ (f a))) r) (\f → bind₀ β (\b → return₀ (f b))))
      ＝⟨⟩
        bind₀ (return₀ createPair) (\r → bind₀ (bind₀ α (\a → return₀ (r a))) (\f → bind₀ β (\b → return₀ (f b))))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ (bind₀ α (\a → return₀ (createPair a))) (\f → bind₀ β (\b → return₀ (f b)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (return₀ (createPair a)) (\f → bind₀ β (\b → return₀ (f b))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → (\f → bind₀ β (\b → return₀ (f b))) (createPair a))
      ＝⟨⟩
        bind₀ α (\a → bind₀ β (\b → return₀ (a , b)))
      ＝⟨⟩
        fpair (Monad-to-ProductiveFunctor monad) α β
      ＝-qed
    ))) where
      return₀ : {A : Set i} → A → F A
      return₀ = return monad
      bind₀ : {A B : Set i} → F A → (A → F B) → F B
      bind₀ = bind monad
      applicative : Applicative F
      applicative = Monad-to-Applicative monad


Monad-to-LiftA02-to-Applicative : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → LiftA02-to-Applicative (Monad-to-LiftA02 monad) ＝ Monad-to-Applicative monad
Monad-to-LiftA02-to-Applicative {i} {F} monad =
  Applicative-Eq
    _
    _
    (\{A} → ＝-refl _)
    (\{A B} → fun-ext _ _ (\(Ff : F (A → B)) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        ap (LiftA02-to-Applicative lifta02) Ff α
      ＝⟨⟩
        liftA2 lifta02 (id (A → B)) Ff α
      ＝⟨⟩
        bind₀ Ff (\f → bind₀ α (\a → return₀ ((id (A → B)) f a)))
      ＝⟨⟩
        bind₀ Ff (\f → bind₀ α (\a → return₀ (f a)))
      ＝⟨⟩
        ap (Monad-to-Applicative monad) Ff α
      ＝-qed
    ))) where
      lifta02 : LiftA02 F
      lifta02 = Monad-to-LiftA02 monad
      return₀ : {A : Set i} → A → F A
      return₀ = return monad
      bind₀ : {A B : Set i} → F A → (A → F B) → F B
      bind₀ = bind monad


Monad-to-LiftA02-to-ProductiveFunctor : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → LiftA02-to-ProductiveFunctor (Monad-to-LiftA02 monad) ＝ Monad-to-ProductiveFunctor monad
Monad-to-LiftA02-to-ProductiveFunctor {i} {F} monad =
  ProductiveFunctor-Eq
    _
    _
    (
      ＝-begin
        ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (Monad-to-LiftA02 monad))
      ＝⟨ LiftA02-to-ProductiveFunctor-to-FunctorWithUnit-Eq (Monad-to-LiftA02 monad) ⟩
        LiftA02-to-FunctorWithUnit (Monad-to-LiftA02 monad)
      ＝⟨ Monad-to-LiftA02-to-FunctorWithUnit-Eq monad ⟩
        Monad-to-FunctorWithUnit monad
      ＝⟨- Monad-to-ProductiveFunctor-to-FunctorWithUnit-Eq monad ⟩
        ProductiveFunctor-to-FunctorWithUnit (Monad-to-ProductiveFunctor monad)
      ＝-qed
    )
    (\A B → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        fpair (LiftA02-to-ProductiveFunctor lifta02) α β
      ＝⟨⟩
        liftA2 lifta02 createPair α β
      ＝⟨⟩
        bind₀ α (\a → bind₀ β (\b → return₀ (a , b)))
      ＝⟨⟩
        fpair (Monad-to-ProductiveFunctor monad) α β
      ＝-qed
    ))) where
      lifta02 : LiftA02 F
      lifta02 = Monad-to-LiftA02 monad
      return₀ : {A : Set i} → A → F A
      return₀ = return monad
      bind₀ : {A B : Set i} → F A → (A → F B) → F B
      bind₀ = bind monad

Monad-to-ProductiveFunctor-to-Applicative : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → ProductiveFunctor-to-Applicative (Monad-to-ProductiveFunctor monad) ＝ Monad-to-Applicative monad
Monad-to-ProductiveFunctor-to-Applicative {i} {F} monad =
  Applicative-Eq
    _
    _
    (\{A} → ＝-refl _)
    (\{A B} → fun-ext _ _ (\(Ff : F (A → B)) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        ap (ProductiveFunctor-to-Applicative pfunctor) Ff α
      ＝⟨⟩
        pfmap pfunctor pMapApply (fpair pfunctor Ff α)
      ＝⟨⟩
        bind₀ (bind₀ Ff (\f → bind₀ α (\a → return₀ (f , a)))) (\r → return₀ (pMapApply r))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ Ff (\f → bind₀ (bind₀ α (\a → return₀ (f , a))) (\r → return₀ (pMapApply r)))
      ＝⟨ fun-eq (\x → bind₀ Ff x) (fun-ext _ _ (\f → Bind-Composition monad _ _ _)) ⟩
        bind₀ Ff (\f → bind₀ α (\a → bind₀ (return₀ (f , a)) (\r → return₀ (pMapApply r))))
      ＝⟨ fun-eq (\x → bind₀ Ff x) (fun-ext _ _ (\f → fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)))) ⟩
        bind₀ Ff (\f → bind₀ α (\a → return₀ (pMapApply (f , a))))
      ＝⟨⟩
        bind₀ Ff (\f → bind₀ α (\a → return₀ (f a)))
      ＝⟨⟩
        ap (Monad-to-Applicative monad) Ff α
      ＝-qed
    ))) where
      pfunctor : ProductiveFunctor F
      pfunctor = Monad-to-ProductiveFunctor monad
      return₀ : {A : Set i} → A → F A
      return₀ = return monad
      bind₀ : {A B : Set i} → F A → (A → F B) → F B
      bind₀ = bind monad

Monad-to-ProductiveFunctor-to-LiftA02 : {i : Level} → {F : Set i → Set i} → (monad : Monad F) → ProductiveFunctor-to-LiftA02 (Monad-to-ProductiveFunctor monad) ＝ Monad-to-LiftA02 monad
Monad-to-ProductiveFunctor-to-LiftA02 {i} {F} monad =
  LiftA02-Eq
    _
    _
    (\{A} → ＝-refl _)
    (\{A B C} → fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        liftA2 (ProductiveFunctor-to-LiftA02 pfunctor) f α β
      ＝⟨⟩
        pfmap pfunctor (\p → f (fst p) (snd p)) (fpair pfunctor α β)
      ＝⟨⟩
        bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ (a , b)))) (\p → return₀ (f (fst p) (snd p)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (bind₀ β (\b → return₀ (a , b))) (\p → return₀ (f (fst p) (snd p))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\(a : A) → Bind-Composition monad _ _ _)) ⟩
        bind₀ α (\a → bind₀ β (\b → bind₀ (return₀ (a , b)) (\p → return₀ (f (fst p) (snd p)))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\(a : A) → fun-eq (\x → bind₀ β x) (fun-ext _ _ (\(b : B) → Return-Left-Identity monad _ _)))) ⟩
        bind₀ α (\a → bind₀ β (\b → return₀ (f a b)))
      ＝⟨⟩
        liftA2 (Monad-to-LiftA02 monad) f α β
      ＝-qed
    )))) where
      pfunctor : ProductiveFunctor F
      pfunctor = Monad-to-ProductiveFunctor monad
      return₀ : {A : Set i} → A → F A
      return₀ = return monad
      bind₀ : {A B : Set i} → F A → (A → F B) → F B
      bind₀ = bind monad
