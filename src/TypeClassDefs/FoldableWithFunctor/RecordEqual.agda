{-# OPTIONS --prop #-}

module TypeClassDefs.FoldableWithFunctor.RecordEqual where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Functor
open import TypeClassDefs.Monoid
open import TypeClassDefs.FoldableWithFunctor.Def

private

  record Body {i} (F : Set i → Set i) : Set (lsuc i) where
    field
      FoldableWithFunctor-to-Functor : Functor F
      fold : {M : Set i} → (monoid : Monoid M) → F M → M

  Body-Explicit : {i : Level} → {F : Set i → Set i} → Functor F → ((M : Set i) → (monoid : Monoid M) → F M → M) → Body F
  Body-Explicit {i} {F} functor₀ fold₀ =
    record {
      FoldableWithFunctor-to-Functor = functor₀
      ; fold = \{M} → \monoid → fold₀ M monoid
    }

  Body-Explicit-Eq : {i : Level} → {F : Set i → Set i} → (functor₁ functor₂ : Functor F) → (fold₁ fold₂ : (M : Set i) → (monoid : Monoid M) → F M → M) → functor₁ ＝ functor₂ → fold₁ ＝ fold₂ → Body-Explicit functor₁ fold₁ ＝ Body-Explicit functor₂ fold₂
  Body-Explicit-Eq
    {i} {F}
    functor₁ functor₂
    fold₁ fold₂
    eq-functor eq-fold
    = ＝-begin
      Body-Explicit functor₁ fold₁
    ＝⟨ fun-eq (\x → Body-Explicit x fold₁) eq-functor ⟩
      Body-Explicit functor₂ fold₁
    ＝⟨ fun-eq (\x → Body-Explicit functor₂ x) eq-fold ⟩
      Body-Explicit functor₂ fold₂
    ＝-qed

  to-Body : {i : Level} → {F : Set i → Set i} → FoldableWithFunctor F → Body F
  to-Body
    record { FoldableWithFunctor-to-Functor = FoldableWithFunctor-to-Functor₀ ; fold = fold₀ }
    = record { FoldableWithFunctor-to-Functor = FoldableWithFunctor-to-Functor₀ ; fold = fold₀ }

  Body-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (Body.FoldableWithFunctor-to-Functor body₁ ＝ Body.FoldableWithFunctor-to-Functor body₂) → ((M : Set i) → Body.fold body₁ {M} ＝ Body.fold body₂ {M}) → body₁ ＝ body₂
  Body-Eq
    {i} {F}
    record { FoldableWithFunctor-to-Functor = functor₁ ; fold = fold₁ }
    record { FoldableWithFunctor-to-Functor = functor₂ ; fold = fold₂ }
    eq-functor eq-fold
    = ＝-begin
      record { FoldableWithFunctor-to-Functor = functor₁ ; fold = fold₁ }
    ＝⟨⟩
      Body-Explicit functor₁ (\M → fold₁ {M})
    ＝⟨ Body-Explicit-Eq functor₁ functor₂ _ _ eq-functor (fun-ext-dep _ _ (\M → eq-fold M)) ⟩
      Body-Explicit functor₂ (\M → fold₂ {M})
    ＝⟨⟩
      record { FoldableWithFunctor-to-Functor = functor₂ ; fold = fold₂ }
    ＝-qed
    

  record Conditions {i} {F : Set i → Set i} (body : Body F) : Prop (lsuc i) where
    fold' : {M : Set i} → (monoid : Monoid M) → F M → M
    fold' = Body.fold body
    fofmap' : {A B : Set i} → (A → B) → F A → F B
    fofmap' = fmap (Body.FoldableWithFunctor-to-Functor body)

    field
      Fold-FmapHomomorphism : {A₁ A₂ M : Set i} → (monoid : Monoid M) → (r : A₂ → M) → (f : A₁ → A₂) → (α : F A₁) → fold' monoid (fofmap' (r ∘ f) α) ＝ fold' monoid (fofmap' r (fofmap' f α))
      Fold-MonoidHomomorphism : {M₁ M₂ : Set i} → (monoid₁ : Monoid M₁) → (monoid₂ : Monoid M₂) → (ψ : M₁ → M₂) → (MonoidHomomorphism monoid₁ monoid₂ ψ) → (α : F M₁) → fold' monoid₂ (fofmap' ψ α) ＝ ψ (fold' monoid₁ α)

  to-Conditions : {i : Level} → {F : Set i → Set i} → (foldable : FoldableWithFunctor F) → Conditions (to-Body foldable)
  to-Conditions
    record { Fold-FmapHomomorphism = Fold-FmapHomomorphism₀ ; Fold-MonoidHomomorphism = Fold-MonoidHomomorphism₀ }
    = record { Fold-FmapHomomorphism = Fold-FmapHomomorphism₀ ; Fold-MonoidHomomorphism = Fold-MonoidHomomorphism₀ }

  to-FoldableWithFunctor : {i : Level} → {F : Set i → Set i} → (body : Body F) → Conditions body → FoldableWithFunctor F
  to-FoldableWithFunctor
    record { FoldableWithFunctor-to-Functor = FoldableWithFunctor-to-Functor₀ ; fold = fold₀ }
    record { Fold-FmapHomomorphism = Fold-FmapHomomorphism₀ ; Fold-MonoidHomomorphism = Fold-MonoidHomomorphism₀ }
    = record { FoldableWithFunctor-to-Functor = FoldableWithFunctor-to-Functor₀ ; fold = fold₀ ; Fold-FmapHomomorphism = Fold-FmapHomomorphism₀ ; Fold-MonoidHomomorphism = Fold-MonoidHomomorphism₀ }

  to-FoldableWithFunctor-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (conditions₁ : Conditions body₁) → (conditions₂ : Conditions body₂) → body₁ ＝ body₂ → to-FoldableWithFunctor body₁ conditions₁ ＝ to-FoldableWithFunctor body₂ conditions₂
  to-FoldableWithFunctor-Eq body₁ body₂ conditions₁ conditions₂ eq-body = proof-irrelevance-with-type _ _ _ to-FoldableWithFunctor body₁ body₂ conditions₁ conditions₂ eq-body

  FoldableWithFunctor-Eq-With-Body : {i : Level} → {F : Set i → Set i} → (foldable₁ foldable₂ : FoldableWithFunctor F) → (to-Body foldable₁ ＝ to-Body foldable₂) → foldable₁ ＝ foldable₂
  FoldableWithFunctor-Eq-With-Body foldable₁ foldable₂ eq-body =
    ＝-begin
      foldable₁
    ＝⟨⟩
      to-FoldableWithFunctor (to-Body foldable₁) (to-Conditions foldable₁)
    ＝⟨ to-FoldableWithFunctor-Eq (to-Body foldable₁) (to-Body foldable₂) (to-Conditions foldable₁) (to-Conditions foldable₂) eq-body ⟩
      to-FoldableWithFunctor (to-Body foldable₂) (to-Conditions foldable₂)
    ＝⟨⟩
      foldable₂
    ＝-qed

FoldableWithFunctor-Eq : {i : Level} → {F : Set i → Set i} → (foldable₁ foldable₂ : FoldableWithFunctor F) → (FoldableWithFunctor-to-Functor foldable₁ ＝ FoldableWithFunctor-to-Functor foldable₂) → ((M : Set i) → fold foldable₁ {M} ＝ fold foldable₂ {M}) → foldable₁ ＝ foldable₂
FoldableWithFunctor-Eq foldable₁ foldable₂ eq-functor eq-fold
  = FoldableWithFunctor-Eq-With-Body foldable₁ foldable₂ (Body-Eq _ _ eq-functor eq-fold)
