{-# OPTIONS --prop #-}

module TypeClassDefs.FoldMapFoldable.RecordEqual where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.Monoid
open import TypeClassDefs.FoldMapFoldable.Def

private
  record Body {i} (T : Set i → Set i) : Set (lsuc i) where
    field
      foldMap : {M : Set i} → (monoid : Monoid M) → {A : Set i} → (A → M) → (T A → M)

  Body-Explicit : {i : Level} → {T : Set i → Set i} → ((M : Set i) → (monoid : Monoid M) → (A : Set i) → (A → M) → (T A → M)) → Body T
  Body-Explicit foldMap₀ = record { foldMap = \{M} → \monoid → \{A} → foldMap₀ M monoid A }

  Body-Explicit-Eq : {i : Level} → {T : Set i → Set i} → (foldMap₁ foldMap₂ : (M : Set i) → (monoid : Monoid M) → (A : Set i) → (A → M) → (T A → M)) → foldMap₁ ＝ foldMap₂ → Body-Explicit foldMap₁ ＝ Body-Explicit foldMap₂
  Body-Explicit-Eq foldMap₀ foldMap₀ (＝-refl foldMap₀) = ＝-refl _

  to-Body : {i : Level} → {T : Set i → Set i} → (foldableWithFoldMap : FoldMapFoldable T) → Body T
  to-Body
    record { foldMap = foldMap₀ }
    = record { foldMap = foldMap₀ }

  Body-Eq : {i : Level} → {T : Set i → Set i} → (body₁ body₂ : Body T) → ({M : Set i} → (monoid : Monoid M) → {A : Set i} → Body.foldMap body₁ {M} monoid {A} ＝ Body.foldMap body₂ {M} monoid {A}) → body₁ ＝ body₂
  Body-Eq
    {i} {T}
    record { foldMap = foldMap₁ }
    record { foldMap = foldMap₂ }
    eq-foldMap
    = ＝-begin
      record { foldMap = foldMap₁ }
    ＝⟨⟩
      Body-Explicit (\M → \monoid → \A → foldMap₁ {M} monoid {A})
    ＝⟨ Body-Explicit-Eq
          _
          _
          (fun-ext-dep _ _ (\M → fun-ext-dep _ _ (\monoid → fun-ext-dep _ _ (\A → eq-foldMap {M} monoid {A}))))
      ⟩
      Body-Explicit (\M → \monoid → \A → foldMap₂ {M} monoid {A})
    ＝⟨⟩
      record { foldMap = foldMap₂ }
    ＝-qed

  record Conditions {i : Level} {T : Set i → Set i} (body : Body T) : Prop (lsuc i) where
    foldMap' : {M : Set i} → (monoid : Monoid M) → {A : Set i} → (A → M) → (T A → M)
    foldMap' = Body.foldMap body

    field
      FoldMap-MonoidHomomorphism :
        {M₁ M₂ : Set i} → {monoid₁ : Monoid M₁} → {monoid₂ : Monoid M₂} →
        (ψ : M₁ → M₂) → MonoidHomomorphism monoid₁ monoid₂ ψ →
        {A : Set i} → (f : A → M₁) → (α : T A) →
        foldMap' monoid₂ (ψ ∘ f) α ＝ ψ (foldMap' monoid₁ f α)

  to-Conditions : {i : Level} → {T : Set i → Set i} → (foldMap : FoldMapFoldable T) → (Conditions (to-Body foldMap))
  to-Conditions
    record { FoldMap-MonoidHomomorphism = FoldMap-MonoidHomomorphism₀ }
    = record { FoldMap-MonoidHomomorphism = FoldMap-MonoidHomomorphism₀ }

  to-FoldMapFoldable : {i : Level} → {T : Set i → Set i} → (body : Body T) → (conditions : Conditions body) → FoldMapFoldable T
  to-FoldMapFoldable
    record { foldMap = foldMap₀}
    record { FoldMap-MonoidHomomorphism = FoldMap-MonoidHomomorphism₀ }
    = record { foldMap = foldMap₀ ; FoldMap-MonoidHomomorphism = FoldMap-MonoidHomomorphism₀ }

  FoldMapFoldable-to-FoldMapFoldable-Eq : {i : Level} → {T : Set i → Set i} → (foldable : FoldMapFoldable T) → foldable ＝ to-FoldMapFoldable (to-Body foldable) (to-Conditions foldable)
  FoldMapFoldable-to-FoldMapFoldable-Eq foldable = ＝-refl _

  to-FoldMapFoldable-Eq : {i : Level} → {T : Set i → Set i} → (body₁ body₂ : Body T) → (conditions₁ : Conditions body₁) → (conditions₂ : Conditions body₂) → body₁ ＝ body₂ → to-FoldMapFoldable body₁ conditions₁ ＝ to-FoldMapFoldable body₂ conditions₂
  to-FoldMapFoldable-Eq body₁ body₂ conditions₁ conditions₂ eq-body = proof-irrelevance-with-type _ _ _ to-FoldMapFoldable body₁ body₂ conditions₁ conditions₂ eq-body

  FoldMapFoldable-Eq-With-Body : {i : Level} → {T : Set i → Set i} → (foldable₁ foldable₂ : FoldMapFoldable T) → to-Body foldable₁ ＝ to-Body foldable₂ → foldable₁ ＝ foldable₂
  FoldMapFoldable-Eq-With-Body foldable₁ foldable₂ eq-body =
    ＝-begin
      foldable₁
    ＝⟨ FoldMapFoldable-to-FoldMapFoldable-Eq foldable₁ ⟩
      to-FoldMapFoldable (to-Body foldable₁) (to-Conditions foldable₁)
    ＝⟨ to-FoldMapFoldable-Eq (to-Body foldable₁) (to-Body foldable₂) (to-Conditions foldable₁) (to-Conditions foldable₂) eq-body ⟩
      to-FoldMapFoldable (to-Body foldable₂) (to-Conditions foldable₂)
    ＝⟨- FoldMapFoldable-to-FoldMapFoldable-Eq foldable₂ ⟩
      foldable₂
    ＝-qed

FoldMapFoldable-Eq : {i : Level} → {T : Set i → Set i} → (foldable₁ foldable₂ : FoldMapFoldable T) → ((M : Set i) → (monoid : Monoid M) → (A : Set i) → foldMap foldable₁ {M} monoid {A} ＝ foldMap foldable₂ {M} monoid {A}) → foldable₁ ＝ foldable₂
FoldMapFoldable-Eq foldable₁ foldable₂ eq-foldMap =
  FoldMapFoldable-Eq-With-Body foldable₁ foldable₂ (Body-Eq (to-Body foldable₁) (to-Body foldable₂) (\{M} → \monoid → \{A} → eq-foldMap M monoid A))
