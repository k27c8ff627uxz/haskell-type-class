{-# OPTIONS --prop #-}

module TypeClassDefs.LiftA02.Def where

open import Agda.Primitive
open import Logic
open import Elements

record LiftA02 {i : Level} (F : Set i → Set i) : Set (lsuc i) where
  field
    liftA0 : {A : Set i} → A → F A
    liftA2 : {A B C : Set i} → (A → B → C) → F A → F B → F C

  liftA1 : {A B : Set i} → (A → B) → F A → F B
  liftA1 {A} {B} f α = liftA2 (id (A → B)) (liftA0 f) α

  liftA3 : {A B C D : Set i} → (A → B → C → D) → F A → F B → F C → F D
  liftA3 {A} {B} {C} {D} f α β γ = liftA2 (id (C → D)) (liftA2 f α β) γ
  
  field
    LiftA2-Identity : {A : Set i} → liftA2 (id (A → A)) (liftA0 (id A)) ＝ id (F A)
    LiftA2-Homomorphism : {A B C : Set i} → (f : A → B → C) → (a : A) → (b : B) → liftA2 f (liftA0 a) (liftA0 b) ＝ liftA0 (f a b)
    LiftA2-Homomorphism2 : {A B C : Set i} → (f : A → B → C) → (α : F A) → (b : B) → liftA2 f α (liftA0 b) ＝ liftA1 (\a → f a b) α
    LiftA2-LiftA1-Composition1 : {A A' B C : Set i} → (f : A' → B → C) → (g : A → A') → (α : F A) → (β : F B) → liftA2 f (liftA1 g α) β ＝ liftA2 (\a → \b → f (g a) b) α β
    LiftA2-LiftA2-Composition1 : {A B C D E : Set i} → (f : C → D → E) → (g : A → B → C) → (α : F A) → (β : F B) → (δ : F D) → liftA2 f (liftA2 g α β) δ ＝ liftA3 (\a → \b → \d → f (g a b) d) α β δ
    LiftA2-LiftA2-Composition2 : {A B C D E : Set i} → (f : C → D → E) → (g : A → B → D) → (α : F A) → (β : F B) → (γ : F C) → liftA2 f γ (liftA2 g α β) ＝ liftA3 (\c → \a → \b → f c (g a b)) γ α β
  
  LiftA1-Homomorphism : {A B : Set i} → (f : A → B) → (a : A) → liftA1 f (liftA0 a) ＝ liftA0 (f a)
  LiftA1-Homomorphism {A} {B} f a =
    ＝-begin
      liftA1 f (liftA0 a)
    ＝⟨⟩
      liftA2 (id (A → B)) (liftA0 f) (liftA0 a)
    ＝⟨ LiftA2-Homomorphism _ f a ⟩
      liftA0 (f a)
    ＝-qed
  
  LiftA2-Homomorphism1 : {A B C : Set i} → (f : A → B → C) → (a : A) → (β : F B) → liftA2 f (liftA0 a) β ＝ liftA1 (\b → f a b) β
  LiftA2-Homomorphism1 {A} {B} {C} f a β =
    ＝-begin
      liftA2 f (liftA0 a) β
    ＝⟨⟩
      liftA2 (\a' → \b → (id (B → C)) (f a') b) (liftA0 a) β
    ＝⟨- LiftA2-LiftA1-Composition1 _ _ _ _ ⟩
      liftA2 (id (B → C)) (liftA1 f (liftA0 a)) β
    ＝⟨ fun-eq (\x → liftA2 (id (B → C)) x β) (LiftA1-Homomorphism f a) ⟩
      liftA2 (id (B → C)) (liftA0 (f a)) β
    ＝⟨⟩
      liftA1 (\b → f a b) β
    ＝-qed

  LiftA3-Homomorphism1 : {A B C D : Set i} → (f : A → B → C → D) → (a : A) → (β : F B) → (γ : F C) → liftA3 f (liftA0 a) β γ ＝ liftA2 (f a) β γ
  LiftA3-Homomorphism1 {A} {B} {C} {D} f a β γ =
    ＝-begin
      liftA3 f (liftA0 a) β γ
    ＝⟨⟩
      liftA2 (id (C → D)) (liftA2 f (liftA0 a) β) γ
    ＝⟨ fun-eq (\x → liftA2 (id (C → D)) x γ) (LiftA2-Homomorphism1 _ _ _) ⟩
      liftA2 (id (C → D)) (liftA1 (\b → f a b) β) γ
    ＝⟨ LiftA2-LiftA1-Composition1 _ _ _ _ ⟩
      liftA2 (\b → \c → (id (C → D)) ((\b' → f a b') b) c) β γ
    ＝⟨⟩
      liftA2 (f a) β γ
    ＝-qed

  LiftA3-Homomorphism2 : {A B C D : Set i} → (f : A → B → C → D) → (α : F A) → (b : B) → (γ : F C) → liftA3 f α (liftA0 b) γ ＝ liftA2 (\a → \c → f a b c) α γ
  LiftA3-Homomorphism2 {A} {B} {C} {D} f α b γ =
    ＝-begin
      liftA3 f α (liftA0 b) γ
    ＝⟨⟩
      liftA2 (id (C → D)) (liftA2 f α (liftA0 b)) γ
    ＝⟨ fun-eq (\x → liftA2 (id (C → D)) x γ) (LiftA2-Homomorphism2 _ _ _) ⟩
      liftA2 (id (C → D)) (liftA1 (\a → f a b) α) γ
    ＝⟨ LiftA2-LiftA1-Composition1 _ _ _ _ ⟩
      liftA2 (\a → \c → (id (C → D)) ((\a' → f a' b) a) c) α γ
    ＝⟨⟩
      liftA2 (\a → \c → f a b c) α γ
    ＝-qed


  LiftA1-LiftA1-Composition : {A B C : Set i} → (f : B → C) → (g : A → B) → (α : F A) → liftA1 f (liftA1 g α) ＝ liftA1 (\a → f (g a)) α
  LiftA1-LiftA1-Composition {A} {B} {C} f g α =
    ＝-begin
      liftA1 f (liftA1 g α)
    ＝⟨⟩
      liftA2 (id (B → C)) (liftA0 f) (liftA2 (id (A → B)) (liftA0 g) α)
    ＝⟨ LiftA2-LiftA2-Composition2 _ _ _ _ _ ⟩
      liftA3 (\f → \g → \a → (id (B → C)) f (id (A → B) g a)) (liftA0 f) (liftA0 g) α
    ＝⟨⟩
      liftA3 (\f → \g → \a → f (g a)) (liftA0 f) (liftA0 g) α
    ＝⟨ LiftA3-Homomorphism1 _ _ _ _ ⟩
      liftA2 (\g → \a → f (g a)) (liftA0 g) α
    ＝⟨ LiftA2-Homomorphism1 _ _ _ ⟩
      liftA1 (\a → f (g a)) α
    ＝-qed

  LiftA1-LiftA2-Composition : {A B C C' : Set i} → (f : C → C') → (g : A → B → C) → (α : F A) → (β : F B) → liftA1 f (liftA2 g α β) ＝ liftA2 (\a → \b → f (g a b)) α β
  LiftA1-LiftA2-Composition {A} {B} {C} {C'} f g α β =
    ＝-begin
      liftA1 f (liftA2 g α β)
    ＝⟨⟩
      liftA2 (id (C → C')) (liftA0 f) (liftA2 g α β)
    ＝⟨ LiftA2-LiftA2-Composition2 _ _ _ _ _ ⟩
      liftA3 (\r → \a → \b → (id (C → C')) r (g a b)) (liftA0 f) α β
    ＝⟨⟩
      liftA3 (\r → \a → \b → r (g a b)) (liftA0 f) α β
    ＝⟨ LiftA3-Homomorphism1 _ _ _ _ ⟩
      liftA2 ((\r → \a → \b → r (g a b)) f) α β
    ＝⟨⟩
      liftA2 (\a → \b → f (g a b)) α β
    ＝-qed
    
  LiftA1-LiftA3-Composition : {A B C D D' : Set i} → (f : D → D') → (g : A → B → C → D) → (α : F A) → (β : F B) → (γ : F C) → liftA1 f (liftA3 g α β γ) ＝ liftA3 (\a → \b → \c → f (g a b c)) α β γ
  LiftA1-LiftA3-Composition {A} {B} {C} {D} {D'} f g α β γ =
    ＝-begin
      liftA1 f (liftA3 g α β γ)
    ＝⟨⟩
      liftA2 (id (D → D')) (liftA0 f) (liftA2 (id (C → D)) (liftA2 g α β) γ)
    ＝⟨ LiftA2-Homomorphism1 _ _ _ ⟩
      liftA1 (\d → (id (D → D')) f d) (liftA2 (id (C → D)) (liftA2 g α β) γ)
    ＝⟨⟩
      liftA1 f (liftA2 (id (C → D)) (liftA2 g α β) γ)
    ＝⟨ LiftA1-LiftA2-Composition _ _ _ _ ⟩
      liftA2 (\r → \c → f ((id (C → D)) r c)) (liftA2 g α β) γ
    ＝⟨⟩
      liftA2 (\r → \c → f (r c)) (liftA2 g α β) γ
    ＝⟨ LiftA2-LiftA2-Composition1 _ _ _ _ _ ⟩
      liftA3 (\a → \b → \c → (\r → \c' → f (r c')) (g a b) c) α β γ
    ＝⟨⟩
      liftA3 (\a → \b → \c → f ((g a b) c)) α β γ
    ＝-qed

  LiftA2-LiftA1-Composition2 : {A B B' C : Set i} → (f : A → B' → C) → (g : B → B') → (α : F A) → (β : F B) → liftA2 f α (liftA1 g β) ＝ liftA2 (\a → \b → f a (g b)) α β
  LiftA2-LiftA1-Composition2 {A} {B} {B'} {C} f g α β =
    ＝-begin
      liftA2 f α (liftA1 g β)
    ＝⟨⟩
      liftA2 f α (liftA2 (id (B → B')) (liftA0 g) β)
    ＝⟨ LiftA2-LiftA2-Composition2 _ _ _ _ _ ⟩
      liftA3 (\a → \r → \b → f a ((id (B → B')) r b)) α (liftA0 g) β
    ＝⟨⟩
      liftA3 (\a → \r → \b → f a (r b)) α (liftA0 g) β
    ＝⟨ LiftA3-Homomorphism2 _ _ _ _ ⟩
      liftA2 (\a → \b → f a (g b)) α β
    ＝-qed
  
  LiftA2-LiftA1-Composition : {A' A B' B C : Set i} → (f : A' → B' → C) → (g₁ : A → A') → (g₂ : B → B') → (α : F A) → (β : F B) → liftA2 f (liftA1 g₁ α) (liftA1 g₂ β) ＝ liftA2 (\a → \b → f (g₁ a) (g₂ b)) α β
  LiftA2-LiftA1-Composition {A'} {A} {B'} {B} {C} f g₁ g₂ α β =
    ＝-begin
      liftA2 f (liftA1 g₁ α) (liftA1 g₂ β)
    ＝⟨ LiftA2-LiftA1-Composition1 _ _ _ _ ⟩
      liftA2 (\a → \b → f (g₁ a) b) α (liftA1 g₂ β)
    ＝⟨ LiftA2-LiftA1-Composition2 _ _ _ _ ⟩
      liftA2 (\a → \b → f (g₁ a) (g₂ b)) α β    ＝-qed
  
open LiftA02 public
