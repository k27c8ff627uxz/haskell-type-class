{-# OPTIONS --prop #-}

module TypeClassDefs.Functor.FunctorRecordEqual where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Functor.Def

private
  record FunctorConditions {i} {F : Set i → Set i} (fmap : ∀(A B : Set i) → (A → B) → (F A → F B)) : Prop (lsuc i) where
    field
      Fmap-Identity : {A : Set i} →  fmap _ _ (id A) ＝ id (F A)
      Fmap-Composition : {A B C : Set i} → {f : B → C} → {g : A → B} → fmap _ _ (f ∘ g) ＝ (fmap _ _ f) ∘ (fmap _ _ g)

  Functor-to-FunctorConditions : {i : Level} → {F : Set i → Set i} → (functor : Functor F) → FunctorConditions (\(A B : Set i) → fmap functor {A} {B})
  Functor-to-FunctorConditions record { fmap = fmap₀ ; Fmap-Identity = Fmap-Identity₀ ; Fmap-Composition = Fmap-Composition₀ }
    = record { Fmap-Identity = Fmap-Identity₀ ; Fmap-Composition = Fmap-Composition₀ }
  
  toFunctor : {i : Level} → {F : Set i → Set i} → (fmap :  ∀ (A B : Set i) → (A → B) → (F A → F B)) → (FunctorConditions fmap) → Functor F
  toFunctor
    fmap₀
    record { Fmap-Identity = Fmap-Identity₀ ; Fmap-Composition = Fmap-Composition₀ }
    = record
        { fmap = fmap₀ _ _ ; Fmap-Identity = Fmap-Identity₀ ; Fmap-Composition = Fmap-Composition₀ }

  Functor-to-toFunctor : {i : Level} → {F : Set i → Set i} → (functor : Functor F) → functor ＝ toFunctor (\(A B : Set i) → fmap functor {A} {B}) (Functor-to-FunctorConditions functor)
  Functor-to-toFunctor record { fmap = fmap₀ ; Fmap-Identity = Fmap-Identity₀ ; Fmap-Composition = Fmap-Composition₀ } = ＝-refl _
  
  toFunctor-Equal : {i : Level} → {F : Set i → Set i} → (fmap₁ fmap₂ : ∀(A B : Set i) → (A → B) → (F A → F B)) → (condition₁ : FunctorConditions fmap₁) → (condition₂ : FunctorConditions fmap₂) → fmap₁ ＝ fmap₂ → toFunctor fmap₁ condition₁ ＝ toFunctor fmap₂ condition₂
  toFunctor-Equal {i} {F} fmap₁ fmap₂ condition₁ condition₂ eq-fmap =
    proof-irrelevance-with-type
    _ _ _ toFunctor
    fmap₁ fmap₂ condition₁ condition₂ eq-fmap

Functor-Equal : {i : Level} → {F : Set i → Set i} → (functor₁ functor₂ : Functor F) → (∀(A B : Set i) → fmap functor₁ {A} {B} ＝ fmap functor₂ {A} {B}) → functor₁ ＝ functor₂
Functor-Equal
  {i} {F}
  functor₁ functor₂
  eq-functor
  =
  ＝-begin
    functor₁
  ＝⟨ Functor-to-toFunctor functor₁ ⟩
    toFunctor (\(A B : Set i) → fmap functor₁ {A} {B}) (Functor-to-FunctorConditions functor₁)
  ＝⟨
      toFunctor-Equal
        _ _ (Functor-to-FunctorConditions functor₁) (Functor-to-FunctorConditions functor₂)
        (fun-ext-dep _ _ (\A → fun-ext-dep _ _ (\B → eq-functor A B)))
    ⟩
    toFunctor (\(A B : Set i) → fmap functor₂ {A} {B}) (Functor-to-FunctorConditions functor₂)
  ＝⟨- Functor-to-toFunctor functor₂ ⟩
    functor₂
  ＝-qed

