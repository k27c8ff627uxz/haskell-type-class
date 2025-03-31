{-# OPTIONS --prop #-}

module Hierarchies.Monad-Applicative where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs

Monad-Applicative : {i : Level} → {F : Set i → Set i} → Monad F → Applicative F
Monad-Applicative {i} {F} monad
  = record {
    pure = pure₀
    ; ap = ap₀
    ; Ap-Identity = \{A} → fun-ext _ _ (\(α : F A) →
      ＝-begin
        ap₀ (pure₀ (id A)) α
      ＝⟨⟩
        bind₀ (return₀ (id A)) (\f → bind₀ α (\a → return₀ (f a)))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ α (\a → return₀ ((id A) a))
      ＝⟨⟩
        bind₀ α return₀
      ＝⟨ Return-Right-Identity monad α ⟩
        α
      ＝⟨⟩
        id (F A) α
      ＝-qed
      )
    ; Ap-Composition = \{A} {B} {C} → \(u : F (B → C)) → \(v : F (A → B)) → \(w : F A) →
      ＝-begin
        ap₀ (ap₀ (ap₀ (pure₀ _∘_) u) v) w
      ＝⟨⟩
        ap₀ (ap₀ (bind₀ (return₀ _∘_) (\F → bind₀ u (\g → return₀ (F g)))) v) w
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x v) w) (Return-Left-Identity monad _ _) ⟩
        ap₀ (ap₀ (bind₀ u (\g → return₀ (_∘_ g))) v) w
      ＝⟨⟩
        ap₀ (bind₀ (bind₀ u (\g → return₀ (_∘_ g))) (\F → bind₀ v (\f → return₀ (F f)))) w
      ＝⟨ fun-eq (\x → ap₀ x w) (Bind-Composition monad _ _ _) ⟩
        ap₀ (bind₀ u (\g → bind₀ ((\g' → return₀ (_∘_ g')) g) (\F → bind₀ v (\f → return₀ (F f))))) w
      ＝⟨⟩
        ap₀ (bind₀ u (\g → bind₀ (return₀ (_∘_ g)) (\F → bind₀ v (\f → return₀ (F f))))) w
      ＝⟨ fun-eq (\x → ap₀ (bind₀ u x) w) (fun-ext _ _ (\g → Return-Left-Identity monad _ _)) ⟩
        ap₀ (bind₀ u (\g → (\F → bind₀ v (\f → return₀ (F f))) (_∘_ g))) w
      ＝⟨⟩
        ap₀ (bind₀ u (\g → bind₀ v (\f → return₀ (g ∘ f)))) w
      ＝⟨⟩
        bind₀ (bind₀ u (\g → bind₀ v (\f → return₀ (g ∘ f)))) (\r → bind₀ w (\t → return₀ (r t)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ u (\q → bind₀ ((\g → bind₀ v (\f → return₀ (g ∘ f))) q) (\r → bind₀ w (\t → return₀ (r t))))
      ＝⟨⟩
        bind₀ u (\q → bind₀ (bind₀ v (\f → return₀ (q ∘ f))) (\r → bind₀ w (\t → return₀ (r t))))
      ＝⟨ fun-eq (\x → bind₀ u x) (fun-ext _ _ (\q → Bind-Composition monad _ _ _)) ⟩
        bind₀ u (\q → bind₀ v (\u → bind₀ ((\f → return₀ (q ∘ f)) u) (\r → bind₀ w (\t → return₀ (r t)))))
      ＝⟨⟩
        bind₀ u (\q → bind₀ v (\f → bind₀ (return₀ (q ∘ f)) (\r → bind₀ w (\t → return₀ (r t)))))
      ＝⟨ fun-eq (\x → bind₀ u x) (fun-ext _ _ (\q → fun-eq (\x → bind₀ v x) (fun-ext _ _ (\f → Return-Left-Identity monad _ _)))) ⟩
        bind₀ u (\q → bind₀ v (\f → (\r → bind₀ w (\t → return₀ (r t))) (q ∘ f)))
      ＝⟨⟩
        bind₀ u (\q → bind₀ v (\f → bind₀ w (\t → return₀ ((q ∘ f) t))))
      ＝⟨⟩
        bind₀ u (\s → bind₀ v (\t → bind₀ w (\n → return₀ (s (t n)))))
      ＝⟨⟩
        bind₀ u (\s → bind₀ v (\t → bind₀ w (\n → (\b → return₀ (s b)) (t n))))
      ＝⟨- fun-eq (\x → bind₀ u x) (fun-ext _ _ (\s → fun-eq (\x → bind₀ v x) (fun-ext _ _ (\t → fun-eq (\x → bind₀ w x) (fun-ext _ _ (\n → Return-Left-Identity monad _ _)))))) ⟩
        bind₀ u (\s → bind₀ v (\t → bind₀ w (\n → bind₀ (return₀ (t n)) (\b → return₀ (s b)))))
      ＝⟨⟩
        bind₀ u (\s → bind₀ v (\t → bind₀ w (\n → bind₀ ((\a → return₀ (t a)) n) (\b → return₀ (s b)))))
      ＝⟨- fun-eq (\x → bind₀ u x) (fun-ext _ _ (\s → fun-eq (\x → bind₀ v x) (fun-ext _ _ (\n → Bind-Composition monad _ _ _)))) ⟩
        bind₀ u (\s → bind₀ v (\t → bind₀ (bind₀ w (\a → return₀ (t a))) (\b → return₀ (s b))))
      ＝⟨⟩
        bind₀ u (\s → bind₀ v (\t → bind₀ ((\r → bind₀ w (\a → return₀ (r a))) t) (\b → return₀ (s b))))
      ＝⟨- fun-eq (\x → bind₀ u x) (fun-ext _ _ (\s → Bind-Composition monad _ _ _)) ⟩
        bind₀ u (\s → bind₀ (bind₀ v (\r → bind₀ w (\a → return₀ (r a)))) (\b → return₀ (s b)))
      ＝⟨⟩
        ap₀ u (bind₀ v (\r → bind₀ w (\a → return₀ (r a))))
      ＝⟨⟩
        ap₀ u (ap₀ v w)
      ＝-qed
    ; Ap-Homomorphism = \{A} {B} → \(f : A → B) → \(a : A) →
      ＝-begin
        ap₀ (pure₀ f) (pure₀ a)
      ＝⟨⟩
        bind₀ (return₀ f) (\f' → bind₀ (return₀ a) (\a' → return₀ (f' a')))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ (return₀ a) (\a' → return₀ (f a'))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        return₀ (f a)
      ＝⟨⟩
        pure₀ (f a)
      ＝-qed
    ; Ap-Interchange = \{A} {B} → \(u : F (A → B)) → \(a : A) →
      ＝-begin
        ap₀ u (pure₀ a)
      ＝⟨⟩
        bind₀ u (\f → bind₀ (return₀ a) (\a' → return₀ (f a')))
      ＝⟨ fun-eq (\x → bind₀ u x) (fun-ext _ _ (\f →
          ＝-begin
            bind₀ (return₀ a) (λ a' → return₀ (f a'))
          ＝⟨ Return-Left-Identity monad _ _ ⟩
            return₀ (f a)
          ＝-qed
        )) ⟩
        bind₀ u (\f → return₀ (f a))
      ＝⟨⟩
        (\s → bind₀ u (\f → return₀ (s f))) (\r → r a)
      ＝⟨- Return-Left-Identity monad _ _ ⟩
        bind₀ (return₀ (\r → r a)) (\s → bind₀ u (\f → return₀ (s f)))
      ＝⟨⟩
        ap₀ (pure₀ (\f → f a)) u
      ＝-qed
  }
  where
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    pure₀ : {A : Set i} → A → F A
    pure₀ = return₀
    ap₀ : {A B : Set i} → F (A → B) → F A → F B
    ap₀ {A} {B} Ff α = bind₀ Ff (\(f : A → B) → bind₀ α (\(a : A) → return₀ (f a)))
  
