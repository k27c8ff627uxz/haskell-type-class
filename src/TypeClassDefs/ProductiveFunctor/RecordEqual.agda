{-# OPTIONS --prop #-}

module TypeClassDefs.ProductiveFunctor.RecordEqual where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.FunctorWithUnit
open import TypeClassDefs.ProductiveFunctor.Def

private
  record Body {i} (F : Set i → Set i) : Set (lsuc i) where
    field
      ProductiveFunctor-to-FunctorWithUnit : FunctorWithUnit F
      fpair : {A B : Set i} → F A → F B → F (Pair A B)


  Body-Explicit : {i : Level} → {F : Set i → Set i} → FunctorWithUnit F → ((A B : Set i) → F A → F B → F (Pair A B)) → Body F
  Body-Explicit {i} {F} ProductiveFunctor-to-FunctorWithUnit₀ fpair₀ = record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₀ ; fpair = \{A B : Set i} → fpair₀ A B }

  Body-Explicit-Eq : {i : Level} → {F : Set i → Set i} (inherit₁ inherit₂ : FunctorWithUnit F) → (fpair₁ fpair₂ : (A B : Set i) → F A → F B → F (Pair A B)) → (inherit₁ ＝ inherit₂) → (fpair₁ ＝ fpair₂) → Body-Explicit inherit₁ fpair₁ ＝ Body-Explicit inherit₂ fpair₂
  Body-Explicit-Eq inherit₀ inherit₀ fpair₀ fpair₀ (＝-refl inherit₀) (＝-refl fpari₀) = ＝-refl _

  to-Body : {i : Level} → {F : Set i → Set i} → ProductiveFunctor F → Body F
  to-Body record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₀ ; fpair = fpair₀ } = record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₀ ; fpair = fpair₀ }

  to-Body-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (Body.ProductiveFunctor-to-FunctorWithUnit body₁ ＝ Body.ProductiveFunctor-to-FunctorWithUnit body₂) → ({A B : Set i} → Body.fpair body₁ {A} {B} ＝ Body.fpair body₂ {A} {B}) → body₁ ＝ body₂
  to-Body-Eq
    {i} {F}
    record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₁ ; fpair = fpair₁ }
    record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₂ ; fpair = fpair₂ }
    eq-ufunctor eq-fpair = ＝-begin
      record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₁ ; fpair = fpair₁ }
    ＝⟨ ＝-refl _ ⟩
      Body-Explicit ProductiveFunctor-to-FunctorWithUnit₁ (\(A B : Set i) → fpair₁ {A} {B})
    ＝⟨
        Body-Explicit-Eq
          ProductiveFunctor-to-FunctorWithUnit₁
          ProductiveFunctor-to-FunctorWithUnit₂
          (\(A B : Set i) → fpair₁ {A} {B})
          (\(A B : Set i) → fpair₂ {A} {B})
          eq-ufunctor
          (fun-ext-dep _ _ (\A → fun-ext-dep _ _ (\B → eq-fpair)))
      ⟩
      Body-Explicit ProductiveFunctor-to-FunctorWithUnit₂ (\(A B : Set i) → fpair₂ {A} {B})
    ＝⟨ ＝-refl _ ⟩
      record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₂ ; fpair = fpair₂ }
    ＝-qed


  record Conditions {i} {F : Set i → Set i} (body : Body F) : Prop (lsuc i) where
    pfmap' : {A B : Set i} → (A → B) → F A → F B
    pfmap' = ufmap (Body.ProductiveFunctor-to-FunctorWithUnit body)

    punit' : {A : Set i} → A → F A
    punit' = unit (Body.ProductiveFunctor-to-FunctorWithUnit body)

    fpair' : {A B : Set i} → F A → F B → F (Pair A B)
    fpair' = Body.fpair body

    field
      Fpair-Homomorphism1 : {A B : Set i} → (a : A) → (β : F B) → fpair' (punit' a) β ＝ pfmap' (\b → (a , b)) β
      Fpair-Homomorphism2 : {A B : Set i} → (α : F A) → (b : B) → fpair' α (punit' b) ＝ pfmap' (\a → (a , b)) α
      Fpair-Associative : {A B C : Set i} → (fa : F A) → (fb : F B) → (fc : F C) → pfmap' (\p → assoc-Pair p) (fpair' (fpair' fa fb) fc) ＝ fpair' fa (fpair' fb fc)
      Fpair-Fmap-Composition : {A A' B B' : Set i} → (f : A → A') → (g : B → B') → (α : F A) → (β : F B) → fpair' (pfmap' f α) (pfmap' g β) ＝ pfmap' (\p → (f (fst p) , g (snd p))) (fpair' α β)
    


  to-Conditions : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → Conditions (to-Body pfunctor)
  to-Conditions
    record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₀ ; fpair = fpair₀ ; Fpair-Homomorphism1 = Fpair-Homomorphism1₀ ; Fpair-Homomorphism2 = Fpair-Homomorphism2₀ ; Fpair-Associative = Fpair-Associative₀ ; Fpair-Fmap-Composition = Fpair-Fmap-Composition₀ }
    = record { Fpair-Homomorphism1 = Fpair-Homomorphism1₀ ; Fpair-Homomorphism2 = Fpair-Homomorphism2₀ ; Fpair-Associative = Fpair-Associative₀ ; Fpair-Fmap-Composition = Fpair-Fmap-Composition₀ }

  to-ProductiveFunctor : {i : Level} → {F : Set i → Set i} → (body : Body F) → (Conditions body) → ProductiveFunctor F
  to-ProductiveFunctor
    record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₀ ; fpair = fpair₀ }
    record { Fpair-Homomorphism1 = Fpair-Homomorphism1₀ ; Fpair-Homomorphism2 = Fpair-Homomorphism2₀ ; Fpair-Associative = Fpair-Associative₀ ; Fpair-Fmap-Composition = Fpair-Fmap-Composition₀ }
    = record { ProductiveFunctor-to-FunctorWithUnit = ProductiveFunctor-to-FunctorWithUnit₀ ; fpair = fpair₀ ; Fpair-Homomorphism1 = Fpair-Homomorphism1₀ ; Fpair-Homomorphism2 = Fpair-Homomorphism2₀ ; Fpair-Associative = Fpair-Associative₀ ; Fpair-Fmap-Composition = Fpair-Fmap-Composition₀ }
    
  ProductiveFunctor-to-ProductiveFunctor-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → pfunctor ＝ to-ProductiveFunctor (to-Body pfunctor) (to-Conditions pfunctor)
  ProductiveFunctor-to-ProductiveFunctor-Eq pfunctor = ＝-refl _

  to-ProductiveFunctor-Eq : {i : Level} → {F : Set i → Set i} → (body₁ body₂ : Body F) → (conditions₁ : Conditions body₁) → (conditions₂ : Conditions body₂) → body₁ ＝ body₂ → to-ProductiveFunctor body₁ conditions₁ ＝ to-ProductiveFunctor body₂ conditions₂
  to-ProductiveFunctor-Eq body₁ body₂ conditions₁ conditions₂ eq-body
    = proof-irrelevance-with-type _ _ _ to-ProductiveFunctor body₁ body₂ conditions₁ conditions₂ eq-body


  ProductiveFunctor-Eq-With-Body : {i : Level} → {F : Set i → Set i} → (pfunctor₁ pfunctor₂ : ProductiveFunctor F) → to-Body pfunctor₁ ＝ to-Body pfunctor₂ → pfunctor₁ ＝ pfunctor₂
  ProductiveFunctor-Eq-With-Body pfunctor₁ pfunctor₂ eq-body =
    ＝-begin
      pfunctor₁
    ＝⟨ ProductiveFunctor-to-ProductiveFunctor-Eq pfunctor₁ ⟩
      to-ProductiveFunctor (to-Body pfunctor₁) (to-Conditions pfunctor₁)
    ＝⟨
        to-ProductiveFunctor-Eq
          (to-Body pfunctor₁)
          (to-Body pfunctor₂)
          (to-Conditions pfunctor₁)
          (to-Conditions pfunctor₂)
          eq-body
      ⟩
      to-ProductiveFunctor (to-Body pfunctor₂) (to-Conditions pfunctor₂)
    ＝⟨- ProductiveFunctor-to-ProductiveFunctor-Eq pfunctor₂ ⟩
      pfunctor₂
    ＝-qed


ProductiveFunctor-Eq : {i : Level} → {F : Set i → Set i} → (pfunctor₁ pfunctor₂ : ProductiveFunctor F) → (ProductiveFunctor-to-FunctorWithUnit pfunctor₁ ＝ ProductiveFunctor-to-FunctorWithUnit pfunctor₂) → ((A B : Set i) → fpair pfunctor₁ {A} {B} ＝ fpair pfunctor₂ {A} {B}) → pfunctor₁ ＝ pfunctor₂
ProductiveFunctor-Eq pfunctor₁ pfunctor₂ eq-ProductiveFunctor-to-FunctorWithUnit eq-fpair =
  ProductiveFunctor-Eq-With-Body pfunctor₁ pfunctor₂ (to-Body-Eq _ _ eq-ProductiveFunctor-to-FunctorWithUnit (\{A B} → eq-fpair A B))

