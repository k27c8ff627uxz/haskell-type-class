{-# OPTIONS --prop #-}

module Hierarchies.Applicative.Factor-Translates where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Applicative.toFunctor
open import Hierarchies.Applicative.Translates
open import Hierarchies.Applicative.Factor-toFunctor

Applicative-to-LiftA02-to-ProductiveFunctor-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → LiftA02-to-ProductiveFunctor (Applicative-to-LiftA02 applicative) ＝ Applicative-to-ProductiveFunctor applicative
Applicative-to-LiftA02-to-ProductiveFunctor-Eq {i} {F} applicative =
  ProductiveFunctor-Eq
    _
    _
    (
      ＝-begin
        ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (Applicative-to-LiftA02 applicative))
      ＝⟨ LiftA02-to-ProductiveFunctor-to-FunctorWithUnit-Eq (Applicative-to-LiftA02 applicative) ⟩
        LiftA02-to-FunctorWithUnit (Applicative-to-LiftA02 applicative)
      ＝⟨ Applicative-to-LiftA02-to-FunctorWithUnit-Eq applicative ⟩
        Applicative-to-FunctorWithUnit applicative
      ＝⟨- Applicative-to-ProductiveFunctor-to-FunctorWithUnit-Eq applicative ⟩
        ProductiveFunctor-to-FunctorWithUnit (Applicative-to-ProductiveFunctor applicative)
      ＝-qed
    )
    (\A B → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        fpair (LiftA02-to-ProductiveFunctor (Applicative-to-LiftA02 applicative)) α β
      ＝⟨⟩
        liftA2 (Applicative-to-LiftA02 applicative) createPair α β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ createPair) α) β
      ＝⟨⟩
        fpair (Applicative-to-ProductiveFunctor applicative) α β
      ＝-qed
    ))) where
      pure₀ : {A : Set i} → A → F A
      pure₀ = pure applicative
      ap₀ : {A B : Set i} → F (A → B) → F A → F B
      ap₀ = ap applicative

Applicative-to-ProductiveFunctor-to-LiftA02-Eq : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → ProductiveFunctor-to-LiftA02 (Applicative-to-ProductiveFunctor applicative) ＝ Applicative-to-LiftA02 applicative
Applicative-to-ProductiveFunctor-to-LiftA02-Eq {i} {F} applicative =
  LiftA02-Eq
    _
    _
    (\{A} → ＝-refl _)
    (\{A B C} → fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\(α : F A) → fun-ext _ _ \(β : F B) →
      ＝-begin
        liftA2 (ProductiveFunctor-to-LiftA02 (Applicative-to-ProductiveFunctor applicative)) f α β
      ＝⟨⟩
        pfmap pfunctor (\p → f (fst p) (snd p)) (fpair pfunctor α β)
      ＝⟨⟩
        ap₀ (pure₀ (\p → f (fst p) (snd p))) (ap₀ (ap₀ (pure₀ createPair) α) β)
      ＝⟨- Ap-Composition applicative _ _ _ ⟩
        ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (\p → f (fst p) (snd p)))) (ap₀ (pure₀ createPair) α)) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x (ap₀ (pure₀ createPair) α)) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (_∘_ (\p → f (fst p) (snd p)))) (ap₀ (pure₀ createPair) α)) β
      ＝⟨- fun-eq (\x → ap₀ x β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (_∘_ (\p → f (fst p) (snd p))))) (pure₀ createPair)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ x (pure₀ createPair)) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (_∘_ (\p → f (fst p) (snd p))))) (pure₀ createPair)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (_∘_ (_∘_ (\p → f (fst p) (snd p))) createPair)) α) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (\a → (_∘_ (\p → f (fst p) (snd p))) (\b → (a , b)))) α) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (\a → \b → (\p → f (fst p) (snd p)) (a , b))) α) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) α) β
      ＝⟨⟩
        liftA2 (Applicative-to-LiftA02 applicative) f α β
      ＝-qed
    ))) where
      pfunctor : ProductiveFunctor F
      pfunctor = Applicative-to-ProductiveFunctor applicative
      pure₀ : {A : Set i} → A → F A
      pure₀ = pure applicative
      ap₀ : {A B : Set i} → F (A → B) → F A → F B
      ap₀ = ap applicative

LiftA02-to-Applicative-to-ProductiveFunctor-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → Applicative-to-ProductiveFunctor (LiftA02-to-Applicative lifta02) ＝ LiftA02-to-ProductiveFunctor lifta02
LiftA02-to-Applicative-to-ProductiveFunctor-Eq {i} {F} lifta02 =
  ProductiveFunctor-Eq
    _
    _
    (
      ＝-begin
        ProductiveFunctor-to-FunctorWithUnit (Applicative-to-ProductiveFunctor (LiftA02-to-Applicative lifta02))
      ＝⟨ Applicative-to-ProductiveFunctor-to-FunctorWithUnit-Eq (LiftA02-to-Applicative lifta02) ⟩
        Applicative-to-FunctorWithUnit (LiftA02-to-Applicative lifta02)
      ＝⟨ LiftA02-to-Applicative-to-FunctorWithUnit-Eq lifta02 ⟩
        LiftA02-to-FunctorWithUnit lifta02
      ＝⟨ LiftA02-to-ProductiveFunctor-to-FunctorWithUnit-Eq lifta02 ⟩
        ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor lifta02)
      ＝-qed
    )
    (\A B → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        fpair (Applicative-to-ProductiveFunctor applicative) α β
      ＝⟨⟩
        ap applicative (ap applicative (pure applicative createPair) α) β
      ＝⟨⟩
        liftA2₀ (id (B → (Pair A B))) (liftA2₀ (id (A → B → Pair A B)) (liftA0₀ createPair) α) β
      ＝⟨ LiftA2-LiftA2-Composition1 lifta02 _ _ _ α β ⟩
        liftA3₀ (\r → \a → \b → (id (B → (Pair A B))) ((id (A → B → Pair A B)) r a) b) (liftA0₀ createPair) α β
      ＝⟨⟩
        liftA3₀ (\r → \a → \b → ((id (A → B → Pair A B)) r a) b) (liftA0₀ createPair) α β
      ＝⟨⟩
        liftA3₀ (\r → \a → \b → r a b) (liftA0₀ createPair) α β
      ＝⟨⟩
        liftA3₀ (id (A → B → Pair A B)) (liftA0₀ createPair) α β
      ＝⟨ LiftA3-Homomorphism1 lifta02 _ _ _ _ ⟩
        liftA2₀ ((id (A → B → Pair A B)) createPair) α β
      ＝⟨⟩
        liftA2₀ createPair α β
      ＝⟨⟩
        fpair (LiftA02-to-ProductiveFunctor lifta02) α β
      ＝-qed
    )))
      where
        applicative : Applicative F
        applicative = LiftA02-to-Applicative lifta02
        liftA0₀ : {A : Set i} → A → F A
        liftA0₀ = liftA0 lifta02
        liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
        liftA2₀ = liftA2 lifta02
        liftA3₀ : {A B C D : Set i} → (A → B → C → D) → F A → F B → F C → F D
        liftA3₀ = liftA3 lifta02

LiftA02-to-ProductiveFunctor-to-Applicative-Eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → ProductiveFunctor-to-Applicative (LiftA02-to-ProductiveFunctor lifta02) ＝ LiftA02-to-Applicative lifta02
LiftA02-to-ProductiveFunctor-to-Applicative-Eq {i} {F} lifta02 =
  Applicative-Eq
    _
    _
    (\{A} → ＝-refl _)
    (\{A} {B} → fun-ext _ _ (\(Ff : F (A → B)) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        ap (ProductiveFunctor-to-Applicative pfunctor) Ff α
      ＝⟨⟩
        pfmap pfunctor pMapApply (fpair pfunctor Ff α)
      ＝⟨⟩
        liftA1₀ pMapApply (liftA2₀ createPair Ff α)
      ＝⟨ LiftA1-LiftA2-Composition lifta02 _ _ _ _ ⟩
        liftA2₀ (\r → \a → pMapApply (createPair r a)) Ff α
      ＝⟨⟩
        liftA2₀ (\r → \a → pMapApply (r , a)) Ff α
      ＝⟨⟩
        liftA2₀ (id (A → B)) Ff α
      ＝⟨⟩
        ap (LiftA02-to-Applicative lifta02) Ff α
      ＝-qed
    ))) where
      pfunctor : ProductiveFunctor F
      pfunctor = LiftA02-to-ProductiveFunctor lifta02
      liftA0₀ : {A : Set i} → A → F A
      liftA0₀ = liftA0 lifta02
      liftA1₀ : {A B : Set i} → (A → B) → F A → F B
      liftA1₀ = liftA1 lifta02
      liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
      liftA2₀ = liftA2 lifta02

ProductiveFunctor-to-Applicative-to-LiftA02-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → Applicative-to-LiftA02 (ProductiveFunctor-to-Applicative pfunctor) ＝ ProductiveFunctor-to-LiftA02 pfunctor
ProductiveFunctor-to-Applicative-to-LiftA02-Eq {i} {F} pfunctor =
  LiftA02-Eq
    _
    _
    (\{A} → ＝-refl _)
    (\{A B C} → fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        liftA2 (Applicative-to-LiftA02 applicative) f α β
      ＝⟨⟩
        ap applicative (ap applicative (pure applicative f) α) β
      ＝⟨⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ pMapApply (fpair₀ (punit₀ f) α)) β)
      ＝⟨ fun-eq (\x → pfmap₀ pMapApply (fpair₀ (pfmap₀ pMapApply x) β)) (Fpair-Homomorphism1 pfunctor _ _) ⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ pMapApply (pfmap₀ (\a → (f , a)) α)) β)
      ＝⟨- fun-eq (\x → pfmap₀ pMapApply (fpair₀ x β)) (PFmap-Composition' pfunctor _) ⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ (pMapApply ∘ (\a → (f , a))) α) β)
      ＝⟨⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ (\a → pMapApply (f , a)) α) β)
      ＝⟨⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ f α) β)
      ＝⟨ fun-eq (\x → pfmap₀ pMapApply x) (Fpair-Fmap-Composition1 pfunctor _ _ _) ⟩
        pfmap₀ pMapApply (pfmap₀ (\p → (f (fst p) , snd p)) (fpair₀ α β))
      ＝⟨- PFmap-Composition' pfunctor _ ⟩
        pfmap₀ (pMapApply ∘ (\p → (f (fst p) , snd p))) (fpair₀ α β)
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (fpair₀ α β)
      ＝⟨⟩
        liftA2 (ProductiveFunctor-to-LiftA02 pfunctor) f α β
      ＝-qed
    )))) where
      applicative : Applicative F
      applicative = ProductiveFunctor-to-Applicative pfunctor
      fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
      fpair₀ = fpair pfunctor
      pfmap₀ : {A B : Set i} → (A → B) → F A → F B
      pfmap₀ = pfmap pfunctor
      punit₀ : {A : Set i} → A → F A
      punit₀ = punit pfunctor

ProductiveFunctor-to-LiftA02-to-Applicative-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → LiftA02-to-Applicative (ProductiveFunctor-to-LiftA02 pfunctor) ＝ ProductiveFunctor-to-Applicative pfunctor
ProductiveFunctor-to-LiftA02-to-Applicative-Eq {i} {F} pfunctor =
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
        pfmap₀ (\p → (id (A → B)) (fst p) (snd p)) (fpair₀ Ff α)
      ＝⟨⟩
        pfmap₀ (\p → (fst p) (snd p)) (fpair₀ Ff α)
      ＝⟨⟩
        pfmap₀ pMapApply (fpair₀ Ff α)
      ＝⟨⟩
        ap (ProductiveFunctor-to-Applicative pfunctor) Ff α
      ＝-qed
    ))) where
      lifta02 : LiftA02 F
      lifta02 = ProductiveFunctor-to-LiftA02 pfunctor
      fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
      fpair₀ = fpair pfunctor
      pfmap₀ : {A B : Set i} → (A → B) → F A → F B
      pfmap₀ = pfmap pfunctor
      punit₀ : {A : Set i} → A → F A
      punit₀ = punit pfunctor
