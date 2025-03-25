{-# OPTIONS --prop #-}

module Logic.ProofIrrelevance where

open Agda.Primitive
open import Logic.Equality

postulate proof-irrelevance : {i j k : Level} → (P : Prop i) → (C : Set k) → (F : P → C) → (p₁ p₂ : P) → F p₁ ＝ F p₂

proof-irrelevance-with-type : {i j k : Level} → (A : Set i) → (P : A → Prop j) → (C : Set k) → (F : (a : A) → P a → C) → (a₁ a₂ : A) → (p₁ : P a₁) → (p₂ : P a₂) → a₁ ＝ a₂ → F a₁ p₁ ＝ F a₂ p₂
proof-irrelevance-with-type {i} {j} {k} A P C F a a p₁ p₂ (＝-refl a) = proof-irrelevance {j} {i} {k} (P a) C (λ p → F a p) p₁ p₂
