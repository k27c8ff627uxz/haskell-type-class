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

MonoidHomomorphism-from-End : {i : Level} → {M : Set i} → (monoid : Monoid M) → MonoidHomomorphism monoid (End-is-Monoid M) (mappend monoid)
MonoidHomomorphism-from-End {i} {M} monoid
  = record {
    MonoidHomomorphism-Empty = fun-ext _ _ (\m →
      ＝-begin
        mappend monoid (mempty monoid) m
      ＝⟨ Mempty-Left-Identity monoid _ ⟩
        m
      ＝⟨⟩
        (id M) m
      ＝⟨⟩
        mempty (End-is-Monoid M) m
      ＝-qed
    )
    ; MonoidHomomorphism-Append = \(m₁ m₂ : M) → fun-ext _ _ (\(n : M) →
      ＝-begin
        mappend monoid (mappend monoid m₁ m₂) n
      ＝⟨ Mappend-Assoc monoid m₁ m₂ n ⟩
        mappend monoid m₁ (mappend monoid m₂ n)
      ＝⟨⟩
        mappend (End-is-Monoid M) (mappend monoid m₁) (mappend monoid m₂) n
      ＝-qed
    )
  }

FoldrFoldable-to-FoldMapFoldable : {i : Level} → {T : Set i → Set i} → FoldrFoldable T → FoldMapFoldable T
FoldrFoldable-to-FoldMapFoldable {i} {T} foldable =
  record {
    foldMap = foldMap₀
    ; FoldMap-MonoidHomomorphism =
        \{M₁ M₂ : Set i} → \{monoid₁} → \{monoid₂} → \(ψ : M₁ → M₂) → \monoid-homomorphism → \{A} → \(f : A → M₁) → \(α : T A) →
          ＝-begin
            foldMap₀ monoid₂ (ψ ∘ f) α
          ＝⟨⟩
            foldr₀ (\a → \b → mappend monoid₂ ((ψ ∘ f) a) b) (mempty monoid₂) α
          ＝⟨ Foldr-MonoidHomomorphism foldable ψ monoid-homomorphism f α ⟩
            ψ (foldr₀ (\a → \b → mappend monoid₁ (f a) b) (mempty monoid₁) α)
          ＝⟨⟩
            ψ (foldMap₀ monoid₁ f α)
          ＝-qed
  } where
    foldr₀ : {A B : Set i} → (A → B → B) → B → T A → B
    foldr₀ = foldr foldable
    foldMap₀ : {M : Set i} → (monoid : Monoid M) → {A : Set i} → (A → M) → (T A → M)
    foldMap₀ {M} monoid {A} f α = foldr₀ (\a → \b → mappend monoid (f a) b) (mempty monoid) α

FoldMapFoldable-to-FoldrFoldable : {i : Level} → {T : Set i → Set i} → FoldMapFoldable T → FoldrFoldable T
FoldMapFoldable-to-FoldrFoldable {i} {T} foldable =
  record {
    foldr = foldr₀
    ; Foldr-MonoidHomomorphism =
      \{M₁ M₂ : Set i} → \{monoid₁ : Monoid M₁} → \{monoid₂ : Monoid M₂} → \(ψ : M₁ → M₂) → \monoid-homomorphism → \{A : Set i} → \(f : A → M₁) → \(α : T A) →
        ＝-begin
          foldr₀ (\a → mappend monoid₂ ((ψ ∘ f) a)) (mempty monoid₂) α
        ＝⟨⟩
          foldMap₀ (End-is-Monoid M₂) (\a → mappend monoid₂ ((ψ ∘ f) a)) α (mempty monoid₂)
        ＝⟨ fun-eq (\x → x (mempty monoid₂)) (FoldMap-MonoidHomomorphism foldable _ (MonoidHomomorphism-from-End monoid₂) _ α) ⟩
          (mappend monoid₂ (foldMap₀ monoid₂ (\a → (ψ ∘ f) a) α)) (mempty monoid₂)
        ＝⟨ fun-eq (\x → mappend monoid₂ x (mempty monoid₂)) (FoldMap-MonoidHomomorphism foldable _ monoid-homomorphism _ α) ⟩
          mappend monoid₂ (ψ (foldMap₀ monoid₁ f α)) (mempty monoid₂)
        ＝⟨- fun-eq (\x → mappend monoid₂ (ψ (foldMap₀ monoid₁ f α)) x) (
            ＝-begin
              ψ (mempty monoid₁)
            ＝⟨ MonoidHomomorphism-Empty {i} {M₁} {M₂} {monoid₁} {monoid₂} monoid-homomorphism ⟩
              mempty monoid₂
            ＝-qed
          ) ⟩
          mappend monoid₂ (ψ (foldMap₀ monoid₁ f α)) (ψ (mempty monoid₁))
        ＝⟨- MonoidHomomorphism-Append monoid-homomorphism _ _ ⟩
          ψ (mappend monoid₁ (foldMap₀ monoid₁ f α) (mempty monoid₁))
        ＝⟨- fun-eq (\x → ψ (x (mempty monoid₁))) (FoldMap-MonoidHomomorphism foldable _ (MonoidHomomorphism-from-End monoid₁) _ α) ⟩
          ψ (foldMap₀ (End-is-Monoid M₁) (\a → mappend monoid₁ (f a)) α (mempty monoid₁))
        ＝⟨⟩
          ψ (foldr₀ (\a → mappend monoid₁ (f a)) (mempty monoid₁) α)
        ＝-qed
    ; Foldr-Destruct = \{A B : Set i} → \(f : A → B → B) → \(α : T A) → \(b : B) → (
        ＝-begin
          foldr₀ f b α
        ＝⟨⟩
          foldMap₀ (End-is-Monoid B) f α b
        ＝⟨⟩
          ((\r₁ → \r₂ → \b → r₁ (r₂ b)) (foldMap₀ (End-is-Monoid B) f α)) (id B) b
        ＝⟨- fun-eq (\x → x (id B) b) ( FoldMap-MonoidHomomorphism foldable _ (MonoidHomomorphism-from-End (End-is-Monoid B)) f α ) ⟩
          (foldMap₀ (End-is-Monoid (B → B)) ((\(r₁ : B → B) → \(r₂ : B → B) → \(b : B) → r₁ (r₂ b)) ∘ f) α (id B)) b
        ＝⟨⟩
          (foldMap₀ (End-is-Monoid (B → B)) (\a → (\r b₁ → f a (r b₁))) α (id B)) b
        ＝⟨⟩
          foldr₀ (\a r b₁ → f a (r b₁)) (id B) α b
        ＝-qed
      )
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
      ＝⟨⟩
        foldMap foldable (End-is-Monoid M) ((mappend monoid) ∘ f) α (mempty monoid)
      ＝⟨ fun-eq
            (\x → x (mempty monoid))
            (FoldMap-MonoidHomomorphism foldable (mappend monoid) (MonoidHomomorphism-from-End monoid) f α)
        ⟩
        ((mappend monoid) (foldMap foldable monoid f α)) (mempty monoid)
      ＝⟨⟩
        mappend monoid (foldMap foldable monoid f α) (mempty monoid)
      ＝⟨ Mempty-Right-Identity monoid _ ⟩
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
      ＝⟨- Foldr-Destruct foldable f α b ⟩
        foldr foldable f b α
      ＝-qed
    ))))
