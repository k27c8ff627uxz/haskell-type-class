{-# OPTIONS --prop #-}

module TypeClassDefs.FoldrFoldable.RecordEqual where

open import Agda.Primitive
open import Logic
open import TypeClassDefs.FoldrFoldable.Def

private
  record Body {i} (T : Set i → Set i) : Set (lsuc i) where
    field
      foldr : {A B : Set i} → (A → B → B) → B → T A → B

  Body-Explicit : {i : Level} → {T : Set i → Set i} → ((A B : Set i) → (A → B → B) → B → T A → B) → Body T
  Body-Explicit {i} {T} foldr₀ = record { foldr = \{A} {B} → foldr₀ A B }

  Body-Explicit-Eq : {i : Level} → {T : Set i → Set i} → (foldr₁ foldr₂ : (A B : Set i) → (A → B → B) → B → T A → B) → foldr₁ ＝ foldr₂ → Body-Explicit foldr₁ ＝ Body-Explicit foldr₂
  Body-Explicit-Eq {i} {T} foldr₀ foldr₀ (＝-refl foldr₀) = ＝-refl _

  to-Body : {i : Level} → {T : Set i → Set i} → FoldrFoldable T → Body T
  to-Body record { foldr = foldr₀ } = record { foldr = foldr₀ }

  to-Body-Eq : {i : Level} → {T : Set i → Set i} → (body₁ body₂ : Body T) → ({A B : Set i} → Body.foldr body₁ {A} {B} ＝ Body.foldr body₂ {A} {B}) → body₁ ＝ body₂
  to-Body-Eq
    {i} {T}
    record { foldr = foldr₁ }
    record { foldr = foldr₂ }
    eq-foldr
    = ＝-begin
      record {foldr = foldr₁ }
    ＝⟨⟩
      Body-Explicit (\A B → foldr₁ {A} {B})
    ＝⟨ Body-Explicit-Eq (\A B → foldr₁ {A} {B}) (\A B → foldr₂ {A} {B}) (fun-ext-dep _ _ (\A → fun-ext-dep _ _ (\B → eq-foldr {A} {B}))) ⟩
      Body-Explicit (\A B → foldr₂ {A} {B})
    ＝⟨⟩
      record {foldr = foldr₂ }
    ＝-qed

  record Conditions {i : Level} {T : Set i → Set i} (body : Body T) : Prop (lsuc i) where

  to-Conditions : {i : Level} → {T : Set i → Set i} → (foldable : FoldrFoldable T) → Conditions (to-Body foldable)
  to-Conditions
    record {}
    = record {}

  to-FoldrFoldable : {i : Level} → {T : Set i → Set i} → (body : Body T) → (conditions : Conditions body) → FoldrFoldable T
  to-FoldrFoldable
    {i} {T}
    record { foldr = foldr₀ }
    record {}
    = record { foldr = foldr₀ }

  FoldrFoldable-to-FoldrFoldable-Eq : {i : Level} → {T : Set i → Set i} → (foldable : FoldrFoldable T) → foldable ＝ to-FoldrFoldable (to-Body foldable) (to-Conditions foldable)
  FoldrFoldable-to-FoldrFoldable-Eq foldable = ＝-refl _

  to-FoldrFoldable-Eq : {i : Level} → {T : Set i → Set i} → (body₁ body₂ : Body T) → (conditions₁ : Conditions body₁) → (conditions₂ : Conditions body₂) → body₁ ＝ body₂ → to-FoldrFoldable body₁ conditions₁ ＝ to-FoldrFoldable body₂ conditions₂
  to-FoldrFoldable-Eq {i} {T} body₁ body₂ conditions₁ conditions₂ eq-body = proof-irrelevance-with-type _ _ _ to-FoldrFoldable body₁ body₂ conditions₁ conditions₂ eq-body

  FoldrFoldable-Eq-With-Body : {i : Level} → {T : Set i → Set i} → (foldable₁ foldable₂ : FoldrFoldable T) → to-Body foldable₁ ＝ to-Body foldable₂ → foldable₁ ＝ foldable₂
  FoldrFoldable-Eq-With-Body foldable₁ foldable₂ eq-body =
    ＝-begin
      foldable₁
    ＝⟨ FoldrFoldable-to-FoldrFoldable-Eq foldable₁ ⟩
      to-FoldrFoldable (to-Body foldable₁) (to-Conditions foldable₁)
    ＝⟨
        to-FoldrFoldable-Eq
          (to-Body foldable₁)
          (to-Body foldable₂)
          (to-Conditions foldable₁)
          (to-Conditions foldable₂)
          eq-body
      ⟩
      to-FoldrFoldable (to-Body foldable₂) (to-Conditions foldable₂)
    ＝⟨- FoldrFoldable-to-FoldrFoldable-Eq foldable₂ ⟩
      foldable₂
    ＝-qed

FoldrFoldable-Eq : {i : Level} → {T : Set i → Set i} → (foldable₁ foldable₂ : FoldrFoldable T) → ((A B : Set i) → foldr foldable₁ {A} {B} ＝ foldr foldable₂ {A} {B}) → foldable₁ ＝ foldable₂
FoldrFoldable-Eq foldable₁ foldable₂ eq-foldr =
  FoldrFoldable-Eq-With-Body
    foldable₁
    foldable₂
    (to-Body-Eq (to-Body foldable₁) (to-Body foldable₂) (\{A} {B} → eq-foldr A B))
