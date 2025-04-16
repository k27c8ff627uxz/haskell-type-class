{-# OPTIONS --prop #-}

module Hierarchies.Foldable where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs


End-is-Monoid : {i : Level} → (A : Set i) → Monoid (A → A)
End-is-Monoid {i} A =
  record {
    mempty = mempty₀
    ; mappend = mappend₀
    ; Mempty-Left-Identity = \(f : A → A) → fun-ext _ _ (\(a : A) →
      ＝-begin
        (mappend₀ mempty₀ f) a
      ＝⟨⟩
        f a
      ＝-qed
    )
    ; Mempty-Right-Identity = \(f : A → A) → fun-ext _ _ (\(a : A) →
      ＝-begin
        (mappend₀ f mempty₀) a
      ＝⟨⟩
        f a
      ＝-qed
    )
    ; Mappend-Assoc = \(f g h : A → A) → fun-ext _ _ (\(a : A) →
      ＝-begin
        mappend₀ (mappend₀ f g) h a
      ＝⟨⟩
        mappend₀ f (mappend₀ g h) a
      ＝-qed
    )
  } where
    mempty₀ : A → A
    mempty₀ = id A
    mappend₀ : (A → A) → (A → A) → (A → A)
    mappend₀ = _∘_

FoldrFoldable-to-FoldMapFoldable : {i : Level} → {T : Set i → Set i} → FoldrFoldable T → FoldMapFoldable T
FoldrFoldable-to-FoldMapFoldable {i} {T} foldable =
  record {
    foldMap = foldMap₀
  } where
    foldr₀ : {A B : Set i} → (A → B → B) → B → T A → B
    foldr₀ = foldr foldable
    foldMap₀ : {M : Set i} → (monoid : Monoid M) → {A : Set i} → (A → M) → (T A → M)
    foldMap₀ {M} monoid {A} f α = foldr₀ (\a → \b → mappend monoid (f a) b) (mempty monoid) α

FoldMapFoldable-to-FoldrFoldable : {i : Level} → {T : Set i → Set i} → FoldMapFoldable T → FoldrFoldable T
FoldMapFoldable-to-FoldrFoldable {i} {T} foldable =
  record {
    foldr = foldr₀
  } where
    foldMap₀ : {M : Set i} → (monoid : Monoid M) → {A : Set i} → (A → M) → (T A → M)
    foldMap₀ = foldMap foldable
    foldr₀ : {A B : Set i} → (A → B → B) → B → T A → B
    foldr₀ {A} {B} f b α = foldMap₀ (End-is-Monoid B) (\a → f a) α b


retract-FoldrFoldable-to-FoldMapFoldable : {i : Level} → {T : Set i → Set i} → (foldable : FoldMapFoldable T) → FoldrFoldable-to-FoldMapFoldable (FoldMapFoldable-to-FoldrFoldable foldable) ＝ foldable
retract-FoldrFoldable-to-FoldMapFoldable {i} {T} foldable =
  FoldMapFoldable-Eq
    _
    foldable
    (\M → \monoid → \A → fun-ext _ _ (\(f : A → M) → fun-ext _ _ (\(α : T A) →
      ＝-begin
        foldMap (FoldrFoldable-to-FoldMapFoldable (FoldMapFoldable-to-FoldrFoldable foldable)) monoid f α
      ＝⟨⟩
        foldr (FoldMapFoldable-to-FoldrFoldable foldable) (\a → \b → mappend monoid (f a) b) (mempty monoid) α
      ＝⟨⟩
        foldMap foldable (End-is-Monoid M) (\a → (\a' → \b → mappend monoid (f a') b) a) α (mempty monoid)
      ＝⟨⟩
        foldMap foldable (End-is-Monoid M) (\a → (\m → mappend monoid (f a) m)) α (mempty monoid)
      ＝⟨ {!!} ⟩
        foldMap foldable monoid f α
      ＝-qed
    )))

retract-FoldMapFoldable-to-FoldrFoldable : {i : Level} → {T : Set i → Set i} → (foldable : FoldrFoldable T) → FoldMapFoldable-to-FoldrFoldable (FoldrFoldable-to-FoldMapFoldable foldable) ＝ foldable
retract-FoldMapFoldable-to-FoldrFoldable {i} {T} foldable =
  FoldrFoldable-Eq
    _
    foldable
    (\(A B : Set i) → fun-ext _ _ (\(f : A → B → B) → fun-ext _ _ (\(b : B) → fun-ext _ _ (\(α : T A) →
      ＝-begin
        foldr (FoldMapFoldable-to-FoldrFoldable (FoldrFoldable-to-FoldMapFoldable foldable)) f b α
      ＝⟨⟩
        foldMap (FoldrFoldable-to-FoldMapFoldable foldable) (End-is-Monoid B) (\a → f a) α b
      ＝⟨⟩
        foldr foldable (\a → \b → mappend (End-is-Monoid B) ((\a' → f a') a) b) (mempty (End-is-Monoid B)) α b
      ＝⟨⟩
        foldr foldable (\a → \b → mappend (End-is-Monoid B) (f a) b) (mempty (End-is-Monoid B)) α b
      ＝⟨⟩
        foldr foldable (\a → \(r : B → B) → \b → f a (r b)) (id B) α b
      ＝⟨ {!!} ⟩
        foldr foldable f b α
      ＝-qed
    ))))
