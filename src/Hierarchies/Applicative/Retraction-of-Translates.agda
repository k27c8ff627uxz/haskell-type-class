{-# OPTIONS --prop #-}

module Hierarchies.Applicative.Retraction-of-Translates where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Applicative.toFunctor
open import Hierarchies.Applicative.Translates
open import Hierarchies.Applicative.Factor-toFunctor

retract-Applicative-to-LiftA02 : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → Applicative-to-LiftA02 (LiftA02-to-Applicative lifta02) ＝ lifta02
retract-Applicative-to-LiftA02 {i} {F} lifta02 =
  LiftA02-Eq
    _
    lifta02
    (\{A} → fun-ext _ _ (\(a : A) →
      ＝-begin
        liftA0 (Applicative-to-LiftA02 (LiftA02-to-Applicative lifta02)) a
      ＝⟨⟩
        pure₀ a
      ＝⟨⟩
        liftA0₀ a
      ＝-qed
    ))
    (\{A} {B} {C} → (fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        liftA2 (Applicative-to-LiftA02 (LiftA02-to-Applicative lifta02)) f α β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) α) β
      ＝⟨⟩
        ap₀ (liftA2₀ (id (A → B → C)) (liftA0₀ f) α) β
      ＝⟨⟩
        liftA2₀ (id (B → C)) (liftA2₀ (id (A → B → C)) (liftA0₀ f) α) β
      ＝⟨ fun-eq (\x → liftA2₀ (id (B → C)) x β) (LiftA2-Homomorphism1 lifta02 _ _ _) ⟩
        liftA2₀ (id (B → C)) (liftA1₀ (\a → id (A → B → C) f a) α) β
      ＝⟨⟩
        liftA2₀ (id (B → C)) (liftA1₀ f α) β
      ＝⟨ LiftA2-LiftA1-Composition1 lifta02 _ _ _ _ ⟩
        liftA2₀ (\a → \b → (id (B → C)) (f a) b) α β
      ＝⟨⟩
        liftA2₀ f α β
      ＝-qed
    )))))
  where
    pure₀ : {A : Set i} → A → F A
    pure₀ = pure (LiftA02-to-Applicative lifta02)
    ap₀ : {A B : Set i} → (F (A → B)) → F A → F B
    ap₀ = ap (LiftA02-to-Applicative lifta02)
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ = liftA0 lifta02
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ = liftA2 lifta02
    liftA1₀ : {A B : Set i} → (A → B) → F A → F B
    liftA1₀ {A} {B} f = liftA2₀ (id (A → B)) (liftA0₀ f)

retract-Applicative-to-ProductiveFunctor : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → Applicative-to-ProductiveFunctor (ProductiveFunctor-to-Applicative pfunctor) ＝ pfunctor
retract-Applicative-to-ProductiveFunctor {i} {F} pfunctor =
  ProductiveFunctor-Eq
    _
    pfunctor
    (
      ＝-begin
        ProductiveFunctor-to-FunctorWithUnit (Applicative-to-ProductiveFunctor (ProductiveFunctor-to-Applicative pfunctor))
      ＝⟨ Applicative-to-ProductiveFunctor-to-FunctorWithUnit-Eq (ProductiveFunctor-to-Applicative pfunctor) ⟩
        Applicative-to-FunctorWithUnit (ProductiveFunctor-to-Applicative pfunctor)
      ＝⟨ ProductiveFunctor-to-Applicative-to-FunctorWithUnit-Eq pfunctor ⟩
        ProductiveFunctor-to-FunctorWithUnit pfunctor
      ＝-qed
    )
    (\A B → fun-ext _ _ (\α → fun-ext _ _ (\β →
      ＝-begin
        fpair (Applicative-to-ProductiveFunctor (ProductiveFunctor-to-Applicative pfunctor)) α β
      ＝⟨⟩
        fpair (Applicative-to-ProductiveFunctor applicative) α β
      ＝⟨⟩
        ap applicative (ap applicative (pure applicative createPair) α) β
      ＝⟨⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ pMapApply (fpair₀ (punit₀ createPair) α)) β)
      ＝⟨ fun-eq (\x → pfmap₀ pMapApply (fpair₀ (pfmap₀ pMapApply x) β)) (Fpair-Homomorphism1 pfunctor _ _) ⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ pMapApply (pfmap₀ (\a → (createPair , a)) α)) β)
      ＝⟨- fun-eq (\x → pfmap₀ pMapApply (fpair₀ x β)) (PFmap-Composition' pfunctor α) ⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ (pMapApply ∘ (\a → (createPair , a))) α) β)
      ＝⟨⟩
        pfmap₀ pMapApply (fpair₀ (pfmap₀ createPair α) β)
      ＝⟨ fun-eq (\x → pfmap₀ pMapApply x) (Fpair-Fmap-Composition1 pfunctor _ _ _) ⟩
        pfmap₀ pMapApply (pfmap₀ (\p → (createPair (fst p) , snd p)) (fpair₀ α β))
      ＝⟨- PFmap-Composition' pfunctor _ ⟩
        pfmap₀ (pMapApply ∘ (\p → (createPair (fst p) , snd p))) (fpair₀ α β)
      ＝⟨⟩
        pfmap₀ (\p → (createPair (fst p)) (snd p)) (fpair₀ α β)
      ＝⟨⟩
        pfmap₀ (\p → (fst p , snd p)) (fpair₀ α β)
      ＝⟨⟩
        pfmap₀ (id _) (fpair₀ α β)
      ＝⟨ fun-eq (\x → x (fpair₀ α β)) (PFmap-Identity pfunctor) ⟩
        id (F _) (fpair₀ α β)
      ＝⟨⟩
        fpair₀ α β
      ＝⟨⟩
        fpair pfunctor α β
      ＝-qed
    ))) where
      applicative : Applicative F
      applicative = ProductiveFunctor-to-Applicative pfunctor
      fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
      fpair₀ = fpair pfunctor
      punit₀ : {A : Set i} → A → F A
      punit₀ = punit pfunctor
      pfmap₀ : {A B : Set i} → (A → B) → F A → F B
      pfmap₀ = pfmap pfunctor


retract-LiftA02-to-Applicative : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → LiftA02-to-Applicative (Applicative-to-LiftA02 applicative) ＝ applicative
retract-LiftA02-to-Applicative {i} {F} applicative
  = Applicative-Eq
    _
    applicative
    (
      ＝-begin
        pure (LiftA02-to-Applicative (Applicative-to-LiftA02 applicative))
      ＝⟨⟩
        liftA0 (Applicative-to-LiftA02 applicative)
      ＝⟨⟩
        pure applicative
      ＝-qed
    )
    \{A} {B} → fun-ext _ _ (\(ψ : F (A → B)) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        ap (LiftA02-to-Applicative (Applicative-to-LiftA02 applicative)) ψ α
      ＝⟨⟩
        liftA2 (Applicative-to-LiftA02 applicative) (id (A → B)) ψ α
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (id (A → B))) ψ) α
      ＝⟨ fun-eq (\x → ap₀ (x ψ) α) (Ap-Identity applicative) ⟩
        ap₀ (id (F (A → B)) ψ) α
      ＝⟨⟩
        ap₀ ψ α
      ＝-qed
    ))
    where
      pure₀ : {A : Set i} → A → F A
      pure₀ = pure applicative
      ap₀ : {A B : Set i} → F (A → B) → F A → F B
      ap₀ = ap applicative

retract-LiftA02-to-ProductiveFunctor : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor) ＝ pfunctor
retract-LiftA02-to-ProductiveFunctor {i} {F} pfunctor
  = ProductiveFunctor-Eq
    _
    pfunctor
    (
      FunctorWithUnit-Eq
        _
        _
        (
          Functor-Equal
          _ _
          (\A B →
            ＝-begin
              fmap (FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor))))
            ＝⟨⟩
              ufmap (ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor)))
            ＝⟨⟩
              pfmap (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor))
            ＝⟨⟩
              ufmap (LiftA02-to-FunctorWithUnit (ProductiveFunctor-to-LiftA02 pfunctor))
            ＝⟨⟩
              fmap (LiftA02-to-Functor (ProductiveFunctor-to-LiftA02 pfunctor))
            ＝⟨⟩
              liftA1 (ProductiveFunctor-to-LiftA02 pfunctor)
            ＝⟨ fun-ext _ _ (\(f : A → B) → fun-ext _ _ (\α →
                ＝-begin
                  liftA1 (ProductiveFunctor-to-LiftA02 pfunctor) f α
                ＝⟨⟩
                  liftA2 (ProductiveFunctor-to-LiftA02 pfunctor) (id (A → B)) (liftA0 (ProductiveFunctor-to-LiftA02 pfunctor) f) α
                ＝⟨⟩
                  pfmap pfunctor (\p → (id (A → B)) (fst p) (snd p)) (fpair pfunctor (punit pfunctor f) α)
                ＝⟨⟩
                  pfmap pfunctor (\p → (fst p) (snd p)) (fpair pfunctor (punit pfunctor f) α)
                ＝⟨ fun-eq (\x → pfmap pfunctor (λ p → fst p (snd p)) x) (Fpair-Homomorphism1 pfunctor _ _) ⟩
                  pfmap pfunctor (\p → (fst p) (snd p)) (pfmap pfunctor (\a → (f , a)) α)
                ＝⟨⟩
                  ((pfmap pfunctor (\p → (fst p) (snd p))) ∘ (pfmap pfunctor (\a → (f , a)))) α
                ＝⟨- fun-eq (\x → x α) (Fmap-Composition (FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit pfunctor))) ⟩
                  pfmap pfunctor ((\p → (fst p) (snd p)) ∘ (\a → (f , a))) α
                ＝⟨⟩
                  pfmap pfunctor f α
                ＝-qed
              )) ⟩
              pfmap pfunctor
            ＝⟨⟩
              ufmap (ProductiveFunctor-to-FunctorWithUnit pfunctor)
            ＝⟨⟩
              fmap (FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit pfunctor))
            ＝-qed
          )
        )
        (\{A} →
          ＝-begin
            unit (ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor)))
          ＝⟨⟩
            punit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor))
          ＝⟨⟩
            liftA0 (ProductiveFunctor-to-LiftA02 pfunctor)
          ＝⟨⟩
            punit pfunctor
          ＝⟨⟩
            unit (ProductiveFunctor-to-FunctorWithUnit pfunctor)
          ＝-qed
        )
    )
    (\A B → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        fpair (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor)) α β
      ＝⟨⟩
        liftA2 (ProductiveFunctor-to-LiftA02 pfunctor) createPair α β
      ＝⟨⟩
        pfmap pfunctor (\p → createPair (fst p) (snd p)) (fpair pfunctor α β)
      ＝⟨⟩
        pfmap pfunctor (\p → (fst p , snd p)) (fpair pfunctor α β)
      ＝⟨⟩
        pfmap pfunctor (id (Pair A B)) (fpair pfunctor α β)
      ＝⟨ fun-eq (\x → x (fpair pfunctor α β)) (PFmap-Identity pfunctor) ⟩
        (id (F (Pair A B))) (fpair pfunctor α β)
      ＝⟨⟩
        fpair pfunctor α β
      ＝-qed
    )))

retract-ProductiveFunctor-to-Applicative : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → ProductiveFunctor-to-Applicative (Applicative-to-ProductiveFunctor applicative) ＝ applicative
retract-ProductiveFunctor-to-Applicative {i} {F} applicative =
  Applicative-Eq
    _
    applicative
    (\{A} → ＝-refl _)
    (\{A B} → fun-ext _ _ (\(Ff : F (A → B)) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        ap (ProductiveFunctor-to-Applicative pfunctor) Ff α
      ＝⟨⟩
        pfmap pfunctor pMapApply (fpair pfunctor Ff α)
      ＝⟨⟩
        ap₀ (pure₀ pMapApply) (ap₀ (ap₀ (pure₀ createPair) Ff) α)
      ＝⟨- Ap-Composition applicative _ _ _ ⟩
        ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ pMapApply)) (ap₀ (pure₀ createPair) Ff)) α
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x (ap₀ (pure₀ createPair) Ff)) α) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (_∘_ pMapApply)) (ap₀ (pure₀ createPair) Ff)) α
      ＝⟨- fun-eq (\x → ap₀ x α) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (_∘_ pMapApply))) (pure₀ createPair)) Ff) α
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ x (pure₀ createPair)) Ff) α) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (_∘_ pMapApply))) (pure₀ createPair)) Ff) α
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x Ff) α) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ ((_∘_ (_∘_ pMapApply)) createPair)) Ff) α
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (\f → (_∘_ pMapApply) (\a → (f , a)))) Ff) α
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (\f → \a → pMapApply (f , a))) Ff) α
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (\f → \a → f a)) Ff) α
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (\f → f)) Ff) α
      ＝⟨ fun-eq (\x → ap₀ (x Ff) α) (Ap-Identity applicative) ⟩
        ap₀ ((id (F (A → B))) Ff) α
      ＝⟨⟩
        ap₀ Ff α
      ＝⟨⟩
        ap applicative Ff α
      ＝-qed
    ))) where
      pfunctor : ProductiveFunctor F
      pfunctor = Applicative-to-ProductiveFunctor applicative
      pure₀ : {A : Set i} → A → F A
      pure₀ = pure applicative
      ap₀ : {A B : Set i} → F (A → B) → F A → F B
      ap₀ = ap applicative

retract-ProductiveFunctor-to-LiftA02 : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → ProductiveFunctor-to-LiftA02 (LiftA02-to-ProductiveFunctor lifta02) ＝ lifta02
retract-ProductiveFunctor-to-LiftA02 {i} {F} lifta02 =
  LiftA02-Eq
    _ lifta02
    (\{A} →
      ＝-begin
        liftA0 (ProductiveFunctor-to-LiftA02 (LiftA02-to-ProductiveFunctor lifta02))
      ＝⟨⟩
        punit (LiftA02-to-ProductiveFunctor lifta02)
      ＝⟨⟩
        liftA0 lifta02
      ＝-qed
    )
    (\{A} {B} {C} → fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        liftA2 (ProductiveFunctor-to-LiftA02 (LiftA02-to-ProductiveFunctor lifta02)) f α β
      ＝⟨⟩
        pfmap (LiftA02-to-ProductiveFunctor lifta02) (\p → f (fst p) (snd p)) (fpair (LiftA02-to-ProductiveFunctor lifta02) α β)
      ＝⟨⟩
        ufmap (LiftA02-to-FunctorWithUnit lifta02) (\p → f (fst p) (snd p)) (liftA2 lifta02 createPair α β)
      ＝⟨⟩
        fmap (LiftA02-to-Functor lifta02) (\p → f (fst p) (snd p)) (liftA2 lifta02 createPair α β)
      ＝⟨⟩
        liftA1 lifta02 (\p → f (fst p) (snd p)) (liftA2 lifta02 createPair α β)
      ＝⟨ LiftA1-LiftA2-Composition lifta02 _ _ _ _ ⟩
        liftA2 lifta02 (\a → \b → (\p → f (fst p) (snd p)) (createPair a b)) α β
      ＝⟨⟩
        liftA2 lifta02 f α β
      ＝-qed
    ))))
