{-# OPTIONS --prop #-}

module Instances.MaybeT.Classes where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Instances.Maybe
open import Instances.MaybeT.Def

MaybeT-Monad : {i : Level} → {M : Set i → Set i} → (monad : Monad M) → Monad (MaybeT monad)
MaybeT-Monad {i} {M} monad =
  record {
    return = return₀
    ; bind = bind₀
    ; Return-Left-Identity = \{A B} → \(f : A → MaybeT monad B) → \(a : A) →
      ＝-begin
        bind₀ (return₀ a) f
      ＝⟨⟩
        bindM (returnM (Just a)) (\oa → MaybeRec oa (returnM Nothing) f)
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        MaybeRec (Just a) (returnM Nothing) f
      ＝⟨⟩
        f a
      ＝-qed
    ; Return-Right-Identity = \{A} → \(α : MaybeT monad A) →
      ＝-begin
        bind₀ α return₀
      ＝⟨⟩
        bindM α (\oa → MaybeRec oa (returnM Nothing) (\a → returnM (Just a)))
      ＝⟨ fun-eq (\x → bindM α x) (fun-ext _ _ (\{ Nothing → ＝-refl _ ; (Just a') → ＝-refl _})) ⟩
        bindM α (\oa → returnM oa)
      ＝⟨ Return-Right-Identity monad _ ⟩
        α
      ＝-qed
    ; Bind-Composition = \{A B C} → \(f : A → MaybeT monad B) → \(g : B → MaybeT monad C) → \(ma : MaybeT monad A) →
      ＝-begin
        bind₀ (bind₀ ma f) g
      ＝⟨⟩
        bindM (bindM ma (\oa → MaybeRec oa (returnM Nothing) f)) (\ob → MaybeRec ob (returnM Nothing) g)
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bindM ma (\oa → bindM (MaybeRec oa (returnM Nothing) f) (\ob → MaybeRec ob (returnM Nothing) g))
      ＝⟨
          fun-eq (\x → bindM ma x) (fun-ext _ _
            \{
              Nothing →
                ＝-begin
                  bindM (MaybeRec Nothing (returnM Nothing) f) (\ob → MaybeRec ob (returnM Nothing) g)
                ＝⟨⟩
                  bindM (returnM Nothing) (\ob → MaybeRec ob (returnM Nothing) g)
                ＝⟨ Return-Left-Identity monad _ _ ⟩
                  MaybeRec Nothing (returnM Nothing) g
                ＝⟨⟩
                  returnM Nothing
                ＝⟨⟩
                  MaybeRec Nothing (returnM Nothing) (\a → bindM (f a) (\ob → MaybeRec ob (returnM Nothing) g))
                ＝-qed
              ; (Just a) →
                ＝-begin
                  bindM (MaybeRec (Just a) (returnM Nothing) f) (\ob → MaybeRec ob (returnM Nothing) g)
                ＝⟨⟩
                  bindM (f a) (\ob → MaybeRec ob (returnM Nothing) g)
                ＝⟨⟩
                  MaybeRec (Just a) (returnM Nothing) (\a → bindM (f a) (\ob → MaybeRec ob (returnM Nothing) g))
                ＝-qed
            }
          )
        ⟩
        bindM ma (\oa → MaybeRec oa (returnM Nothing) (\a → bindM (f a) (\ob → MaybeRec ob (returnM Nothing) g)))
      ＝⟨⟩
        bind₀ ma (\a → bind₀ (f a) g)
      ＝-qed
  } where
    returnM : {A : Set i} → A → M A
    returnM = return monad
    bindM : {A B : Set i} → M A → (A → M B) → M B
    bindM = bind monad
    return₀ : {A : Set i} → A → MaybeT monad A
    return₀ {A} a = returnM (Just a)
    bind₀ : {A B : Set i} → MaybeT monad A → (A → MaybeT monad B) → MaybeT monad B
    bind₀ {A} {B} m f = bindM m (\oa → MaybeRec oa (returnM Nothing) f)
    

MaybeT-MonadTrans : {i : Level} → MonadTrans {i} MaybeT
MaybeT-MonadTrans {i} =
  record {
    MonadTrans-to-Monad = \{M} → \monad → MaybeT-Monad monad
    ; lift = \{M} → \{monad} → \{A} → lift₀ {M} {monad} {A}
    ; MonadTrans-Return = \{M} → \{monad} → \{A} → \(a : A) →
      ＝-begin
        return (MaybeT-Monad monad) a
      ＝⟨⟩
        return monad (Just a)
      ＝⟨- Return-Left-Identity monad _ _ ⟩
        bind monad (return monad a) (\a' → return monad (Just a'))
      ＝⟨⟩
        lift₀ {M} {monad} {A} (return monad a)
      ＝-qed
    ; MonadTrans-Bind = \{M} → \{monad} → \{A B} → \(α : M A) → \(f : A → M B) →
      ＝-begin
        lift₀ {M} {monad} {B} (bind monad α f)
      ＝⟨⟩
        bind monad (bind monad α f) (\b → return monad (Just b))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind monad α (\a → bind monad (f a) (\b → return monad (Just b)))
      ＝⟨⟩
        bind monad α (\a → MaybeRec (Just a) (return monad Nothing) (\a → bind monad (f a) (\b → return monad (Just b))))
      ＝⟨- fun-eq (\x → bind monad α x) (fun-ext _ _ (\(a : A) → Return-Left-Identity monad _ _)) ⟩
        bind monad α (\a → bind monad (return monad (Just a)) (\oa → MaybeRec oa (return monad Nothing) (\a → bind monad (f a) (\b → return monad (Just b)))))
      ＝⟨- Bind-Composition monad _ _ _ ⟩
        bind monad (bind monad α (\a → return monad (Just a))) (\oa → MaybeRec oa (return monad Nothing) (\a → bind monad (f a) (\b → return monad (Just b))))
      ＝⟨⟩
        bind monad (lift₀ {M} {monad} {A} α) (\oa → MaybeRec oa (return monad Nothing) (\a → lift₀ {M} {monad} {B} (f a)))
      ＝⟨⟩
        bind (MaybeT-Monad monad) (lift₀ {M} {monad} {A} α) (\a → lift₀ {M} {monad} {B} (f a))
      ＝-qed
  } where
    lift₀ : {M : Set i → Set i} → {monad : Monad M} → {A : Set i} → M A → MaybeT monad A
    lift₀ {M} {monad} {A} m = bind monad m (\a → return monad (Just a))
