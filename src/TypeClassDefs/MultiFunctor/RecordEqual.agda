{-# OPTIONS --prop #-}

module TypeClassDefs.MultiFunctor.RecordEqual where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.MultiFunctor.Def

private
  record Conditions {i} {F : Set i → Set i} (fmapn : (ltype : List (Set i)) → (A : Set i) → (f : (TypedList ltype) → A) → (TypedList (list-fmap F ltype)) → F A) : Prop (lsuc i) where
    field
      Fmapn-Identity : {A : Set i} → fmapn _ _ (id-TypedList A) ＝ id-TypedList (F A)
      Fmapn-Composition : {typed₁ typed₂ : List (Set i)} → {A B : Set i} → (f : TypedList (A ∷ typed₂) → B) → (g : TypedList typed₁ → A) → (list₁ : TypedList (list-fmap F typed₁)) → (list₂ : TypedList (list-fmap F typed₂)) → fmapn ( typed₁ ⧺ typed₂ ) _ (composition-TypedList {i} {typed₁} {typed₂} f g) (fmap-t++-homomorphism typed₁ typed₂ (list₁ t++ list₂)) ＝ fmapn _ _ f ((fmapn _ _ g list₁) t∷ list₂)


  to-Conditions : {i :  Level} → {F : Set i → Set i} → (mfunctor : MultiFunctor F) → Conditions (\ltype → \A → fmapn mfunctor {ltype} {A})
  to-Conditions
    record { fmapn = fmapn₀ ; Fmapn-Identity = Fmapn-Identity₀ ; Fmapn-Composition = Fmapn-Composition₀ }
    = record { Fmapn-Identity = Fmapn-Identity₀ ; Fmapn-Composition = Fmapn-Composition₀ }

  to-MultiFunctor : {i : Level} → {F : Set i → Set i} → (fmapn₀ : (ltype : List (Set i)) → (A : Set i) → (f : (TypedList ltype) → A) → (TypedList (list-fmap F ltype)) → F A) → (conditions : Conditions fmapn₀) → MultiFunctor F
  to-MultiFunctor fmapn₀ record { Fmapn-Identity = Fmapn-Identity₀ ; Fmapn-Composition = Fmapn-Composition₀ }
    = record { fmapn = \{ltype} → \{A} → fmapn₀ ltype A ; Fmapn-Identity = Fmapn-Identity₀ ; Fmapn-Composition = Fmapn-Composition₀ }

  MultiFunctor-to-MultiFunctor-Eq : {i : Level} → {F : Set i → Set i} → (mfunctor : MultiFunctor F) → mfunctor ＝ to-MultiFunctor (\ltype → \A → fmapn mfunctor {ltype} {A}) (to-Conditions mfunctor)
  MultiFunctor-to-MultiFunctor-Eq mfunctor = ＝-refl _

  to-MultiFunctor-Eq : {i : Level} → {F : Set i → Set i} → (fmapn₁ fmapn₂ : (ltype : List (Set i)) → (A : Set i) → (f : (TypedList ltype) → A) → (TypedList (list-fmap F ltype)) → F A) → (conditions₁ : Conditions fmapn₁) → (conditions₂ : Conditions fmapn₂) → fmapn₁ ＝ fmapn₂ → to-MultiFunctor fmapn₁ conditions₁ ＝ to-MultiFunctor fmapn₂ conditions₂
  to-MultiFunctor-Eq
    {i} {F}
    fmapn₁ fmapn₂
    conditions₁ conditions₂
    eq-fmapn =
      proof-irrelevance-with-type
        _ _ _
        to-MultiFunctor fmapn₁ fmapn₂
        conditions₁ conditions₂
        eq-fmapn

MultiFunctor-Eq : {i : Level} → {F : Set i → Set i} → (mfunctor₁ mfunctor₂ : MultiFunctor F) → ((ltype : List (Set i)) → (A : Set i) → fmapn mfunctor₁ {ltype} {A} ＝ fmapn mfunctor₂ {ltype} {A}) → mfunctor₁ ＝ mfunctor₂
MultiFunctor-Eq
  {i} {F}
  mfunctor₁ mfunctor₂
  eq-fmapn
  = ＝-begin
    mfunctor₁
  ＝⟨ MultiFunctor-to-MultiFunctor-Eq mfunctor₁ ⟩
    to-MultiFunctor (\ltype → \A → fmapn mfunctor₁ {ltype} {A}) (to-Conditions mfunctor₁)
  ＝⟨
      to-MultiFunctor-Eq
        (\ltype → \A → fmapn mfunctor₁ {ltype} {A})
        (\ltype → \A → fmapn mfunctor₂ {ltype} {A})
        (to-Conditions mfunctor₁)
        (to-Conditions mfunctor₂)
        (fun-ext-dep _ _ (\ltype → fun-ext-dep _ _ (\A → eq-fmapn ltype A)))
    ⟩
    to-MultiFunctor (\ltype → \A → fmapn mfunctor₂ {ltype} {A}) (to-Conditions mfunctor₂)
  ＝⟨- MultiFunctor-to-MultiFunctor-Eq mfunctor₂ ⟩
    mfunctor₂
  ＝-qed
