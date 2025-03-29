{-# OPTIONS --prop #-}

module TypeClassDefs.ProductiveFunctor.Def where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs.FunctorWithUnit

record ProductiveFunctor {i} (F : Set i → Set i) : Set (lsuc i) where
  field
    ProductiveFunctor-to-FunctorWithUnit : FunctorWithUnit F
    fpair : {A B : Set i} → F A → F B → F (Pair A B)

  pfmap : {A B : Set i} → (A → B) → F A → F B
  pfmap = ufmap ProductiveFunctor-to-FunctorWithUnit

  punit : {A : Set i} → A → F A
  punit = unit ProductiveFunctor-to-FunctorWithUnit
  
  field
    Fpair-Homomorphism1 : {A B : Set i} → (a : A) → (β : F B) → fpair (punit a) β ＝ pfmap (\b → (a , b)) β
    Fpair-Homomorphism2 : {A B : Set i} → (α : F A) → (b : B) → fpair α (punit b) ＝ pfmap (\a → (a , b)) α
    Fpair-Associative : {A B C : Set i} → (fa : F A) → (fb : F B) → (fc : F C) → pfmap (\p → assoc-Pair p) (fpair (fpair fa fb) fc) ＝ fpair fa (fpair fb fc)
    Fpair-Fmap-Composition : {A A' B B' : Set i} → (f : A → A') → (g : B → B') → (α : F A) → (β : F B) → fpair (pfmap f α) (pfmap g β) ＝ pfmap (\p → (f (fst p) , g (snd p))) (fpair α β)

  PFmap-Identity : {A : Set i} →  pfmap (id A) ＝ id (F A)
  PFmap-Identity = UFmap-Identity ProductiveFunctor-to-FunctorWithUnit
  PFmap-Composition : {A B C : Set i} → {f : B → C} → {g : A → B} → pfmap (f ∘ g) ＝ (pfmap f) ∘ (pfmap g)
  PFmap-Composition = UFmap-Composition ProductiveFunctor-to-FunctorWithUnit
  PUnit-Homomorphism : {A B : Set i} → (a : A) → (f : A → B) → pfmap f (punit a) ＝ punit (f a)
  PUnit-Homomorphism = Unit-Homomorphism ProductiveFunctor-to-FunctorWithUnit

  Fpair-Homomorphism : {A B : Set i} → (a : A) → (b : B) → fpair (punit a) (punit b) ＝ punit ( a , b )
  Fpair-Homomorphism {A} {B} a b =
    ＝-begin
      fpair (punit a) (punit b)
    ＝⟨ Fpair-Homomorphism1 a (punit b) ⟩
      pfmap (\b → (a , b)) (punit b)
    ＝⟨ PUnit-Homomorphism _ _ ⟩
      punit (a , b)
    ＝-qed

  PFmap-Composition' : {A B C : Set i} → {f : B → C} → {g : A → B} → (α : F A) → (pfmap (f ∘ g)) α ＝ pfmap f (pfmap g α)
  PFmap-Composition' {A} {B} {C} {f} {g} α =
    ＝-begin
      (pfmap (f ∘ g)) α
    ＝⟨ fun-eq (\x → x α) PFmap-Composition ⟩
      ((pfmap f) ∘ (pfmap g)) α
    ＝⟨⟩
      pfmap f (pfmap g α)
    ＝-qed

  Fpair-Fmap-Composition1 : {A A' B : Set i} → (f : A → A') → (α : F A) → (β : F B) → fpair (pfmap f α) β ＝ pfmap (\p → (f (fst p) , snd p)) (fpair α β)
  Fpair-Fmap-Composition1 {A} {A'} {B} f α β =
    ＝-begin
      fpair (pfmap f α) β
    ＝⟨⟩
      fpair (pfmap f α) (id (F B) β)
    ＝⟨- fun-eq (\x → fpair (pfmap f α) (x β)) PFmap-Identity ⟩
      fpair (pfmap f α) (pfmap (id B) β)
    ＝⟨ Fpair-Fmap-Composition f (id B) α β ⟩
      pfmap (\p → f (fst p) , (id B (snd p))) (fpair α β)
    ＝⟨⟩
      pfmap (\p → f (fst p) , snd p) (fpair α β)
    ＝-qed

  Fpair-Fmap-Composition2 : {A B B' : Set i} → (g : B → B') → (α : F A) → (β : F B) → fpair α (pfmap g β) ＝ pfmap (\p → (fst p , g (snd p))) (fpair α β)
  Fpair-Fmap-Composition2 {A} {B} {B'} g α β =
    ＝-begin
      fpair α (pfmap g β)
    ＝⟨⟩
      fpair (id (F A) α) (pfmap g β)
    ＝⟨- fun-eq (\x → fpair (x α) (pfmap g β)) PFmap-Identity ⟩
      fpair (pfmap (id A) α) (pfmap g β)
    ＝⟨ Fpair-Fmap-Composition (id A) g α β ⟩
      pfmap (\p → ( (id A) (fst p) , g (snd p))) (fpair α β)
    ＝⟨⟩
      pfmap (\p → (fst p , g (snd p))) (fpair α β)
    ＝-qed
open ProductiveFunctor public
