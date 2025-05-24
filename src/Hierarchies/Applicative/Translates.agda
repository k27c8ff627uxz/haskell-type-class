{-# OPTIONS --prop #-}

module Hierarchies.Applicative.Translates where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Hierarchies.Applicative.toFunctor

Applicative-to-LiftA02 : {i : Level} → {F : Set i → Set i} → Applicative F → LiftA02 F
Applicative-to-LiftA02 {i} {F} applicative =
  record {
    liftA0 = pure₀
    ; liftA2 = liftA2₀
    ; LiftA2-Identity = \{A} →
      ＝-begin
        liftA2₀ (id (A → A)) (liftA0₀ (id A))
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (id (A → A))) (pure₀ (id A)))
      ＝⟨ fun-eq (\x → ap₀ (x (pure₀ (id A)))) (Ap-Identity applicative) ⟩
        ap₀ (id (F (A → A)) (pure₀ (id A)))
      ＝⟨⟩
        ap₀ (pure₀ (id A))
      ＝⟨ Ap-Identity applicative ⟩
        id (F A)
      ＝-qed
    ; LiftA2-Homomorphism = \{A} {B} {C} → \(f : A → B → C) → \(a : A) → \(b : B) →
      ＝-begin
        liftA2₀ f (pure₀ a) (pure₀ b)
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) (pure₀ a)) (pure₀ b)
      ＝⟨ fun-eq (\x → ap₀ x (pure₀ b)) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (pure₀ (f a)) (pure₀ b)
      ＝⟨ Ap-Homomorphism applicative _ _ ⟩
        pure₀ (f a b)
      ＝-qed
    ; LiftA2-Homomorphism2 = \{A} {B} {C} → \(f : A → B → C) → \(α : F A) → \(b : B) →
      ＝-begin
        liftA2₀ f α (liftA0₀ b)
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) α) (pure₀ b)
      ＝⟨ Ap-Interchange applicative _ _ ⟩
        ap₀ (pure₀ (\r → r b)) (ap₀ (pure₀ f) α)
      ＝⟨- Ap-Composition applicative _ _ _ ⟩
        ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (\r → r b))) (pure₀ f)) α
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x (pure₀ f)) α) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (_∘_ (\r → r b))) (pure₀ f)) α
      ＝⟨ fun-eq (\x → ap₀ x α) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (pure₀ (_∘_ (\r → r b) f)) α
      ＝⟨⟩
        ap₀ (pure₀ (\a → f a b)) α
      ＝⟨⟩
        ap₀ (pure₀ ((id (A → C)) (\a → f a b))) α
      ＝⟨- fun-eq (\x → ap₀ x α) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (id (A → C))) (pure₀ (\a → f a b))) α
      ＝⟨⟩
        liftA2₀ (id (A → C)) (liftA0₀ (\a → f a b)) α
      ＝⟨⟩
        liftA1₀ (\a → f a b) α
      ＝-qed
    ; LiftA2-LiftA1-Composition1 = \{A} {A'} {B} {C} → \(f : A' → B → C) → \(g : A → A') → \(α : F A) → \(β : F B) →
      ＝-begin
        liftA2₀ f (liftA2₀ (id (A → A')) (pure₀ g) α) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) (ap₀ (ap₀ (pure₀ (id (A → A'))) (pure₀ g)) α)) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (pure₀ f) (ap₀ x α)) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ f) (ap₀ (pure₀ ((id (A → A')) g)) α)) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) (ap₀ (pure₀ g) α)) β
      ＝⟨- fun-eq (\x → ap₀ x β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ f)) (pure₀ g)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ x (pure₀ g)) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ f)) (pure₀ g)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (_∘_ f g)) α) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (f ∘ g)) α) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (\a → f (g a))) α) β
      ＝⟨⟩
        liftA2₀ (\a → f (g a)) α β
      ＝-qed
    ; LiftA2-LiftA2-Composition1 = \{A} {B} {C} {D} {E} → \(f : C → D → E) → \(g : A → B → C) → \(α : F A) → \(β : F B) → \(δ : F D) → 
      ＝-begin
        liftA2₀ f (liftA2₀ g α β) δ
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) (ap₀ (ap₀ (pure₀ g) α) β)) δ
      ＝⟨- fun-eq (\x → ap₀ x δ) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ f)) (ap₀ (pure₀ g) α)) β) δ
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ x (ap₀ (pure₀ g) α)) β) δ) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ f)) (ap₀ (pure₀ g) α)) β) δ
      ＝⟨- fun-eq (\x → ap₀ (ap₀ x β) δ) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (_∘_ f))) (pure₀ g)) α) β) δ
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ x (pure₀ g)) α) β) δ) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (_∘_ f))) (pure₀ g)) α) β) δ
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ x α) β) δ) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (_∘_ f) g)) α) β) δ
      ＝⟨⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (_∘_ (id (D → E))) (\a → \b → \d → f (g a b) d))) α) β) δ
      ＝⟨- fun-eq (\x → ap₀ (ap₀ (ap₀ x α) β) δ) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (_∘_ (id (D → E))))) (pure₀ (\a → \b → \d → f (g a b) d))) α) β) δ
      ＝⟨- fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ x (pure₀ (\a → \b → \d → f (g a b) d))) α) β) δ) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (_∘_ (id (D → E))))) (pure₀ (\a → \b → \d → f (g a b) d))) α) β) δ
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x β) δ) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (id (D → E)))) (ap₀ (pure₀ (\a → \b → \d → f (g a b) d)) α)) β) δ
      ＝⟨- fun-eq (\x → ap₀ (ap₀ (ap₀ x (ap₀ (pure₀ (λ a → λ b → λ d → f (g a b) d)) α)) β) δ) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (id (D → E)))) (ap₀ (pure₀ (\a → \b → \d → f (g a b) d)) α)) β) δ
      ＝⟨ fun-eq (\x → ap₀ x δ) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (pure₀ (id (D → E))) (ap₀ (ap₀ (pure₀ (\a → \b → \d → f (g a b) d)) α) β)) δ
      ＝⟨⟩
        liftA2₀ (id (D → E)) (liftA2₀ (\a → \b → \d → f (g a b) d) α β) δ
      ＝⟨⟩
        liftA3₀ (\a → \b → \d → f (g a b) d) α β δ
      ＝-qed
    ; LiftA2-LiftA2-Composition2 = \{A} {B} {C} {D} {E} → \(f : C → D → E) → \(g : A → B → D) → \(α : F A) → \(β : F B) → \(γ : F C) →
      ＝-begin
        liftA2₀ f γ (liftA2₀ g α β)
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) γ) (ap₀ (ap₀ (pure₀ g) α) β)
      ＝⟨- Ap-Composition applicative _ _ _ ⟩
        ap₀ (ap₀ (ap₀ (pure₀ _∘_) (ap₀ (pure₀ f) γ)) (ap₀ (pure₀ g) α)) β
      ＝⟨- fun-eq (\x → ap₀ x β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (ap₀ (pure₀ _∘_) (ap₀ (pure₀ f) γ))) (pure₀ g)) α) β
      ＝⟨- fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) x) (pure₀ g)) α) β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ _∘_)) (pure₀ f)) γ)) (pure₀ g)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (ap₀ (ap₀ x (pure₀ f)) γ)) (pure₀ g)) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (ap₀ (ap₀ (pure₀ (_∘_ _∘_)) (pure₀ f)) γ)) (pure₀ g)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (ap₀ x γ)) (pure₀ g)) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (ap₀ (pure₀ ((_∘_ _∘_) f)) γ)) (pure₀ g)) α) β
      ＝⟨- fun-eq (\x → ap₀ (ap₀ (ap₀ x (pure₀ g)) α) β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ _∘_)) (pure₀ ((_∘_ _∘_) f))) γ) (pure₀ g)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ (ap₀ x (pure₀ (_∘_ ∘ f))) γ) (pure₀ g)) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (ap₀ (pure₀ (_∘_ _∘_)) (pure₀ ((_∘_ _∘_) f))) γ) (pure₀ g)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ x γ) (pure₀ g)) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ ((_∘_ _∘_) ((_∘_ _∘_) f))) γ) (pure₀ g)) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x α) β) (Ap-Interchange applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (\r → r g)) (ap₀ (pure₀ ((_∘_ _∘_) ((_∘_ _∘_) f))) γ)) α) β
      ＝⟨- fun-eq (\x → ap₀ (ap₀ x α) β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (\r → r g))) (pure₀ ((_∘_ _∘_) ((_∘_ _∘_) f)))) γ) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ (ap₀ x (pure₀ (_∘_ ∘ (_∘_ ∘ f)))) γ) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (\r → r g))) (pure₀ ((_∘_ _∘_) ((_∘_ _∘_) f)))) γ) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (ap₀ x γ) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ ((_∘_ (\r → r g)) ((_∘_ _∘_) ((_∘_ _∘_) f)))) γ) α) β
      ＝⟨⟩
        ap₀ (ap₀ (ap₀ (pure₀ ((_∘_ (_∘_ (id (B → E)))) (\c → \a → \b → f c (g a b)))) γ) α) β
      ＝⟨- fun-eq (\x → ap₀ (ap₀ (ap₀ x γ) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (_∘_ (id (B → E))))) (pure₀ (\c → \a → \b → f c (g a b)))) γ) α) β
      ＝⟨- fun-eq (λ x → ap₀ (ap₀ (ap₀ (ap₀ x (pure₀ (λ c → λ a → λ b → f c (g a b)))) γ) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (_∘_ (id (B → E))))) (pure₀ (\c → \a → \b → f c (g a b)))) γ) α) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ x α) β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (ap₀ (pure₀ (_∘_ (id (B → E)))) (ap₀ (pure₀ (\c → \a → \b → f c (g a b))) γ)) α) β
      ＝⟨- fun-eq (\x → ap₀ (ap₀ (ap₀ x (ap₀ (pure₀ (λ c → λ a → λ b → f c (g a b))) γ)) α) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (ap₀ (ap₀ (pure₀ _∘_) (pure₀ (id (B → E)))) (ap₀ (pure₀ (\c → \a → \b → f c (g a b))) γ)) α) β
      ＝⟨ fun-eq (\x → ap₀ x β) (Ap-Composition applicative _ _ _) ⟩
        ap₀ (ap₀ (pure₀ (id (B → E))) (ap₀ (ap₀ (pure₀ (\c → \a → \b → f c (g a b))) γ) α)) β
      ＝⟨⟩
        liftA2₀ (id (B → E)) (liftA2₀ (\c → \a → \b → f c (g a b)) γ α) β
      ＝⟨⟩
        liftA3₀ (\c → \a → \b → f c (g a b)) γ α β
      ＝-qed
  } where
    pure₀ : {A : Set i} → A → F A
    pure₀ = pure applicative
    ap₀ : {A B : Set i} → F (A → B) → F A → F B
    ap₀ = ap applicative
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ = pure₀
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ f α = ap₀ (ap₀ (pure₀ f) α)
    liftA1₀ : {A B : Set i} → (A → B) → F A → F B
    liftA1₀ {A} {B} f = liftA2₀ (id (A → B)) (liftA0₀ f)
    liftA3₀ : {A B C D : Set i} → (A → B → C → D) → F A → F B → F C → F D
    liftA3₀ {A} {B} {C} {D} f α β γ = liftA2₀ (id (C → D)) (liftA2₀ f α β) γ


LiftA02-to-Applicative : {i : Level} → {F : Set i → Set i} → LiftA02 F → Applicative F
LiftA02-to-Applicative
  {i} {F} lifta02 =
  record {
      pure = pure₀
      ; ap = ap₀
      ; Ap-Identity = \{A} →
        ＝-begin
          ap₀ (pure₀ (id A))
        ＝⟨⟩
          liftA2₀ (id (A → A)) (liftA0₀ (id A))
        ＝⟨ LiftA2-Identity lifta02 ⟩
          id (F A)
        ＝-qed
      ; Ap-Composition = \{A} {B} {C} → \(u : F (B → C)) → \(v : F (A → B)) → \(w : F A) →
        ＝-begin
          ap₀ (ap₀ (ap₀ (pure₀ _∘_) u) v) w
        ＝⟨⟩
          ap₀ (ap₀ (liftA2₀ (id ((B → C) → (A → B) → (A → C))) (liftA0₀ _∘_) u) v) w
        ＝⟨ fun-eq (\x → ap₀ (ap₀ x v) w) (LiftA2-Homomorphism1 lifta02 _ _ _) ⟩
          ap₀ (ap₀ (liftA1₀ (\f → (id ((B → C) → (A → B) → (A → C))) _∘_ f) u) v) w
        ＝⟨⟩
          ap₀ (ap₀ (liftA1₀ _∘_ u) v) w
        ＝⟨⟩
          ap₀ (liftA2₀ (id ((A → B) → (A → C))) (liftA1₀ _∘_ u) v) w
        ＝⟨ fun-eq (\x → ap₀ x w) (LiftA2-LiftA1-Composition1 lifta02 _ _ _ _) ⟩
          ap₀ (liftA2₀ (\f → \g → (id ((A → B) → (A → C))) (_∘_ f) g) u v) w
        ＝⟨⟩
          ap₀ (liftA2₀ _∘_ u v) w
        ＝⟨⟩
          liftA2₀ (id (A → C)) (liftA2₀ _∘_ u v) w
        ＝⟨ LiftA2-LiftA2-Composition1 lifta02 _ _ _ _ _ ⟩
          liftA3₀ (\f → \g → \a → (id (A → C)) (_∘_ f g) a) u v w
        ＝⟨⟩
          liftA3₀ (\f → \g → \a → f (g a)) u v w
        ＝⟨⟩
          liftA3₀ (\f → \g → \a → (id (B → C)) f ((id (A → B)) g a)) u v w
        ＝⟨- LiftA2-LiftA2-Composition2 lifta02 _ _ _ _ _ ⟩
          liftA2₀ (id (B → C)) u (liftA2₀ (id (A → B)) v w)
        ＝⟨⟩
          ap₀ u (ap₀ v w)
        ＝-qed
      ; Ap-Homomorphism = \{A} → \{B} → \(f : A → B) → \(a : A) →
        ＝-begin
          ap₀ (pure₀ f) (pure₀ a)
        ＝⟨⟩
          liftA2₀ (id (A → B)) (liftA0₀ f) (liftA0₀ a)
        ＝⟨ LiftA2-Homomorphism lifta02 _ _ _ ⟩
          liftA0₀ (f a)
        ＝⟨⟩
          pure₀ (f a)
        ＝-qed
      ; Ap-Interchange = \{A} → \{B} → \(u : F (A → B)) → \(a : A) →
        ＝-begin
          ap₀ u (pure₀ a)
        ＝⟨⟩
          liftA2₀ (id (A → B)) u (liftA0₀ a)
        ＝⟨ LiftA2-Homomorphism2 lifta02 _ _ _ ⟩
          liftA1₀ (\f → (id (A → B)) f a) u
        ＝⟨⟩
          liftA1₀ (\f → f a) u
        ＝⟨⟩
          ap₀ (pure₀ (\f → f a)) u
        ＝-qed
   }
   where
     liftA0₀ : ∀{A} → A → F A
     liftA0₀ = liftA0 lifta02
     liftA1₀ : {A B : Set i} → (A → B) → F A → F B
     liftA1₀ = liftA1 lifta02
     liftA2₀ : ∀{A B C} → (A → B → C) → F A → F B → F C
     liftA2₀ = liftA2 lifta02
     liftA3₀ : {A B C D : Set i} → (A → B → C → D) → F A → F B → F C → F D
     liftA3₀ = liftA3 lifta02
     pure₀ : ∀{A} → A → F A
     pure₀ = liftA0₀
     ap₀ : ∀{A B : Set i} → F (A → B) → F A → F B
     ap₀ {A} {B} Ff α = liftA2₀ (id (A → B)) Ff α

LiftA02-to-ProductiveFunctor : {i : Level} → {F : Set i → Set i} → LiftA02 F → ProductiveFunctor F
LiftA02-to-ProductiveFunctor {i} {F} lifta02 =
  record {
    ProductiveFunctor-to-FunctorWithUnit = ufunctor
    ; fpair = fpair₀
    ; Fpair-Homomorphism1 = \{A} {B} → \(a : A) → \(β : F B) →
      ＝-begin
        fpair₀ (punit₀ a) β
      ＝⟨⟩
        liftA2₀ (\a → \b → (a , b)) (liftA0₀ a) β
      ＝⟨ LiftA2-Homomorphism1 lifta02 _ _ _ ⟩
        liftA1₀ (\b → (\a → \b' → (a , b')) a b) β
      ＝⟨⟩
        liftA1₀ (\b → (a , b)) β
      ＝⟨⟩
        liftA1₀ (\b → (id (B → Pair A B)) (\b' → (a , b')) b) β
      ＝⟨- LiftA2-Homomorphism1 lifta02 _ _ _ ⟩
        liftA2₀ (id (B → Pair A B)) (liftA0₀ (\b → (a , b))) β
      ＝⟨⟩
        pfmap₀ (\b → (a , b)) β
      ＝-qed
    ; Fpair-Homomorphism2 = \{A} {B} → \(α : F A) → \(b : B) →
      ＝-begin
        fpair₀ α (punit₀ b)
      ＝⟨⟩
        liftA2₀ (\a → \b → (a , b)) α (liftA0₀ b)
      ＝⟨ LiftA2-Homomorphism2 lifta02 _ _ _ ⟩
        liftA1₀ (\a' → (\a → \b → (a , b)) a' b) α
      ＝⟨⟩
        liftA1₀ (\a → (a , b)) α
      ＝⟨⟩
        pfmap₀ (\a → (a , b)) α
      ＝-qed
    ; Fpair-Associative = \{A} {B} {C} → \(α : F A) → \(β : F B) → \(γ : F C) →
      ＝-begin
        pfmap₀ (\p → assoc-Pair p) (fpair₀ (fpair₀ α β) γ)
      ＝⟨⟩
        liftA1₀ assoc-Pair (liftA2₀ (\ab → \c → (ab , c)) (liftA2₀ (\a → \b → (a , b)) α β) γ)
      ＝⟨ fun-eq (\x → pfmap₀ assoc-Pair x) (LiftA2-LiftA2-Composition1 lifta02 _ _ _ _ _) ⟩
        liftA1₀ assoc-Pair (liftA3₀ (\a → \b → \c → (\ab' → \c' → (ab' , c')) ((\a' → \b' → (a , b)) a b) c) α β γ)
      ＝⟨⟩
        liftA1₀ assoc-Pair (liftA3₀ (\a → \b → \c → ((a , b) , c)) α β γ)
      ＝⟨ LiftA1-LiftA3-Composition lifta02 _ _ _ _ _ ⟩
        liftA3₀ (\a' → \b' → \c' → assoc-Pair ((\a → \b → \c → ((a , b) , c)) a' b' c')) α β γ
      ＝⟨⟩
        liftA3₀ (\a → \b → \c → assoc-Pair ((a , b) , c)) α β γ 
      ＝⟨⟩
        liftA3₀ (\a → \b → \c → (a , (b , c))) α β γ
      ＝⟨⟩
        liftA3₀ (\a → \b → \c → (\a' → \bc' → (a' , bc')) a ((\b' → \c' → (b , c)) b c)) α β γ
      ＝⟨- LiftA2-LiftA2-Composition2 lifta02 _ _ _ _ _ ⟩
        liftA2₀ (\a → \bc → (a , bc)) α (liftA2₀ (\b → \c → (b , c)) β γ)
      ＝⟨⟩
        fpair₀ α (fpair₀ β γ)
      ＝-qed
    ; Fpair-Fmap-Composition = \{A} {A'} {B} {B'} → \(f : A → A') → \(g : B → B') → \(α : F A) → \(β : F B) →
      ＝-begin
        fpair₀ (pfmap₀ f α) (pfmap₀ g β)
      ＝⟨⟩
        liftA2₀ (\a → \b → (a , b)) (liftA1₀ f α) (liftA1₀ g β)
      ＝⟨ LiftA2-LiftA1-Composition lifta02 _ _ _ _ _ ⟩
        liftA2₀ (\a → \b → (f a , g b)) α β
      ＝⟨⟩
        liftA2₀ (\a → \b → (\p → (f (fst p) , g (snd p))) ((\a' → \b' → (a' , b')) a b)) α β
      ＝⟨- LiftA1-LiftA2-Composition lifta02 _ _ _ _ ⟩
        liftA1₀ (\p → (f (fst p) , g (snd p))) (liftA2₀ (\a → \b → (a , b)) α β)
      ＝⟨⟩
        pfmap₀ (\p → (f (fst p) , g (snd p))) (fpair₀ α β)
      ＝-qed
  }
  where
    ufunctor : FunctorWithUnit F
    ufunctor = LiftA02-to-FunctorWithUnit lifta02
    pfmap₀ : {A B : Set i} → (A → B) → F A → F B
    pfmap₀ = ufmap ufunctor
    punit₀ : {A : Set i} → A → F A
    punit₀ = unit ufunctor
    liftA1₀ : {A B : Set i} → (A → B) → F A → F B
    liftA1₀ = liftA1 lifta02
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ = liftA2 lifta02
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ = liftA0 lifta02
    liftA3₀ : {A B C D : Set i} → (A → B → C → D) → F A → F B → F C → F D
    liftA3₀ = liftA3 lifta02
    fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
    fpair₀ = liftA2₀ (\a → \b → (a , b))

ProductiveFunctor-to-LiftA02 : {i : Level} → {F : Set i → Set i} → ProductiveFunctor F → LiftA02 F
ProductiveFunctor-to-LiftA02 {i} {F} pfunctor =
  record {
    liftA0 = liftA0₀
    ; liftA2 = liftA2₀
    ; LiftA2-Identity = \{A} → fun-ext _ _ (\α →
      ＝-begin
        liftA2₀ (id (A → A)) (liftA0₀ (id A)) α
      ＝⟨⟩
        pfmap₀ (\p → id (A → A) (fst p) (snd p)) (fpair₀ (punit₀ (id A)) α)
      ＝⟨⟩
        pfmap₀ (\p → (fst p) (snd p)) (fpair₀ (punit₀ (id A)) α)
      ＝⟨ fun-eq (\x → pfmap₀ (\p → fst p (snd p)) x) (Fpair-Homomorphism1 pfunctor _ _) ⟩
        pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\a → ((id A) , a)) α)
      ＝⟨⟩
        ((pfmap₀ (\p → (fst p) (snd p))) ∘ (pfmap₀ (\a → (id A , a)))) α
      ＝⟨- fun-eq (\x → x α) (PFmap-Composition pfunctor) ⟩
        (pfmap₀ ((\p → (fst p) (snd p)) ∘ (\a → (id A , a))) α)
      ＝⟨⟩
        pfmap₀ (\a → (id A) a) α
      ＝⟨⟩
        pfmap₀ (id A) α
      ＝⟨ fun-eq (\x → x α) (PFmap-Identity pfunctor) ⟩
        id (F A) α
      ＝-qed
    )
    ; LiftA2-Homomorphism = \{A} {B} {C} → \(f : A → B → C) → \(a : A) → \(b : B) →
      ＝-begin
        liftA2₀ f (liftA0₀ a) (liftA0₀ b)
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (fpair₀ (punit₀ a) (punit₀ b))
      ＝⟨ fun-eq (\x → pfmap₀ (\p → f (fst p) (snd p)) x) (Fpair-Homomorphism pfunctor a b) ⟩
        pfmap₀ (\p → f (fst p) (snd p)) (punit₀ (a , b))
      ＝⟨ PUnit-Homomorphism pfunctor _ _ ⟩
        punit₀ ((\p → f (fst p) (snd p)) (a , b))
      ＝⟨⟩
        punit₀ (f a b)
      ＝⟨⟩
        liftA0₀ (f a b)
      ＝-qed
    ; LiftA2-Homomorphism2 = \{A} {B} {C} → \(f : A → B → C) → \(α : F A) → \(b : B) →
      ＝-begin
        liftA2₀ f α (liftA0₀ b)
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (fpair₀ α (punit₀ b))
      ＝⟨ fun-eq (\x → pfmap₀ (\p → f (fst p) (snd p)) x) (Fpair-Homomorphism2 pfunctor _ _) ⟩
        pfmap₀ (\p → f (fst p) (snd p)) (pfmap₀ (\a → (a , b)) α)
      ＝⟨- PFmap-Composition' pfunctor α ⟩
        pfmap₀ ((\p → f (fst p) (snd p)) ∘ (\a → (a , b))) α
      ＝⟨⟩
        pfmap₀ (\a → f a b) α
      ＝⟨⟩
        pfmap₀ ((\p → (fst p) (snd p)) ∘ (\a → ((\r → f r b) , a))) α
      ＝⟨ PFmap-Composition' pfunctor α ⟩
        pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\a → ((\r → f r b) , a))  α)
      ＝⟨- fun-eq (\x → pfmap₀ (\p → (fst p) (snd p)) x) (Fpair-Homomorphism1 pfunctor _ _) ⟩
        pfmap₀ (\p → (fst p) (snd p)) (fpair₀ (punit₀ (\a → f a b)) α)
      ＝⟨⟩
        pfmap₀ (\p → (id (A → C)) (fst p) (snd p)) (fpair₀ (punit₀ (\a → f a b)) α)
      ＝⟨⟩
        liftA2₀ (id (A → C)) (liftA0₀ (\a → f a b)) α
      ＝-qed
    ; LiftA2-LiftA1-Composition1 = \{A} {A'} {B} {C} → \(f : A' → B → C) → \(g : A → A') → \(α : F A) → \(β : F B) →
      ＝-begin
        liftA2₀ f (liftA2₀ (id (A → A')) (liftA0₀ g) α) β
      ＝⟨⟩
        liftA2₀ f (pfmap₀ (\p → (id (A → A')) (fst p) (snd p)) (fpair₀ (punit₀ g) α)) β
      ＝⟨⟩
        liftA2₀ f (pfmap₀ (\p → (fst p) (snd p)) (fpair₀ (punit₀ g) α)) β
      ＝⟨ fun-eq (\x → liftA2₀ f (pfmap₀ (\p → fst p (snd p)) x) β) (Fpair-Homomorphism1 pfunctor _ _) ⟩
        liftA2₀ f (pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\a → (g , a)) α)) β
      ＝⟨- fun-eq (\x → liftA2₀ f x β) (PFmap-Composition' pfunctor _) ⟩
        liftA2₀ f (pfmap₀ ((\p → (fst p) (snd p)) ∘ (\a → (g , a))) α) β
      ＝⟨⟩
        liftA2₀ f (pfmap₀ g α) β
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (fpair₀ (pfmap₀ g α) β)
      ＝⟨ fun-eq (\x → pfmap₀ (\p → f (fst p) (snd p)) x) (Fpair-Fmap-Composition1 pfunctor _ _ _) ⟩
        pfmap₀ (\p → f (fst p) (snd p)) (pfmap₀ (\p → (g (fst p) , snd p)) (fpair₀ α β))
      ＝⟨- PFmap-Composition' pfunctor _ ⟩
        pfmap₀ ((\p → f (fst p) (snd p)) ∘ (\p → (g (fst p) , snd p))) (fpair₀ α β)
      ＝⟨⟩
        pfmap₀ (\p → f (g (fst p)) (snd p)) (fpair₀ α β)
      ＝⟨⟩
        pfmap₀ (\p → (\a → f (g a)) (fst p) (snd p)) (fpair₀ α β)
      ＝⟨⟩
        liftA2₀ (\a → f (g a)) α β
      ＝-qed
    ; LiftA2-LiftA2-Composition1 = \{A} {B} {C} {D} {E} → \(f : C → D → E) → \(g : A → B → C) → \(α : F A) → \(β : F B) → \(δ : F D) →
      ＝-begin
        liftA2₀ f (liftA2₀ g α β) δ
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (fpair₀ (pfmap₀ (\p → g (fst p) (snd p)) (fpair₀ α β)) δ)
      ＝⟨ fun-eq (\x → pfmap₀ (\p → f (fst p) (snd p)) x) (Fpair-Fmap-Composition1 pfunctor _ _ _) ⟩
        pfmap₀ (\p → f (fst p) (snd p)) (pfmap₀ (\q → ( (\p → g (fst p) (snd p)) (fst q) , snd q)) (fpair₀ (fpair₀ α β) δ))
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (pfmap₀ (\q → (g (fst (fst q)) (snd (fst q)) , snd q)) (fpair₀ (fpair₀ α β) δ))
      ＝⟨- PFmap-Composition' pfunctor _ ⟩
        pfmap₀ ((\p → f (fst p) (snd p)) ∘ (\q → (g (fst (fst q)) (snd (fst q)) , snd q))) (fpair₀ (fpair₀ α β) δ)
      ＝⟨⟩
        pfmap₀ (\q → f (g (fst (fst q)) (snd (fst q))) (snd q)) (fpair₀ (fpair₀ α β) δ)
      ＝⟨⟩
        pfmap₀ ((\p → (fst p) (snd p)) ∘ (\q → ( f (g (fst (fst q)) (snd (fst q))) , snd q))) (fpair₀ (fpair₀ α β) δ)
      ＝⟨ PFmap-Composition' pfunctor _ ⟩
        pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\q → ( f (g (fst (fst q)) (snd (fst q))) , (snd q))) (fpair₀ (fpair₀ α β) δ))
      ＝⟨⟩
        pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\q → ( (\p → f (g (fst p) (snd p))) (fst q) , (snd q))) (fpair₀ (fpair₀ α β) δ))
      ＝⟨- fun-eq (\x → pfmap₀ (\p → fst p (snd p)) x) (Fpair-Fmap-Composition1 pfunctor _ _ _) ⟩
        pfmap₀ (\p → (fst p) (snd p)) (fpair₀ (pfmap₀ (\p → f (g (fst p) (snd p))) (fpair₀ α β)) δ)
      ＝⟨⟩
        pfmap₀ (\p → id (D → E) (fst p) (snd p)) (fpair₀ (pfmap₀ (\p → (\a b → f (g a b)) (fst p) (snd p)) (fpair₀ α β)) δ)
      ＝⟨⟩
        liftA2₀ (id (D → E)) (liftA2₀ (\a b → f (g a b)) α β) δ
      ＝-qed
    ; LiftA2-LiftA2-Composition2 = \{A} {B} {C} {D} {E} → \(f : C → D → E) → \(g : A → B → D) → \(α : F A) → \(β : F B) → \(γ : F C) →
      ＝-begin
        liftA2₀ f γ (liftA2₀ g α β)
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (fpair₀ γ (pfmap₀ (\p → g (fst p) (snd p)) (fpair₀ α β)))
      ＝⟨ fun-eq (\x → pfmap₀ (\p → f (fst p) (snd p)) x) (Fpair-Fmap-Composition2 pfunctor _ _ _) ⟩
        pfmap₀ (\p → f (fst p) (snd p)) (pfmap₀ (\p → (fst p , (\q → g (fst q) (snd q)) (snd p))) (fpair₀ γ (fpair₀ α β)))
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (snd p)) (pfmap₀ (\p → (fst p , g (fst (snd p)) (snd (snd p)))) (fpair₀ γ (fpair₀ α β)))
      ＝⟨- PFmap-Composition' pfunctor _ ⟩
        pfmap₀ ((\p → f (fst p) (snd p)) ∘ (\p → (fst p , g (fst (snd p)) (snd (snd p))))) (fpair₀ γ (fpair₀ α β))
      ＝⟨⟩
        pfmap₀ (\p → f (fst p) (g (fst (snd p)) (snd (snd p)))) (fpair₀ γ (fpair₀ α β))
      ＝⟨- fun-eq (\x → pfmap₀ (\p → f (fst p) (g (fst (snd p)) (snd (snd p)))) x) (Fpair-Associative pfunctor _ _ _) ⟩
        pfmap₀ (\p → f (fst p) (g (fst (snd p)) (snd (snd p)))) (pfmap₀ (\p → assoc-Pair p) (fpair₀ (fpair₀ γ α) β))
      ＝⟨- PFmap-Composition' pfunctor _ ⟩
        pfmap₀ ((\p → f (fst p) (g (fst (snd p)) (snd (snd p)))) ∘ (\p → assoc-Pair p)) (fpair₀ (fpair₀ γ α) β)
      ＝⟨⟩
        pfmap₀ (\p → f (fst (assoc-Pair p)) (g (fst (snd (assoc-Pair p))) (snd (snd (assoc-Pair p))))) (fpair₀ (fpair₀ γ α) β)
      ＝⟨⟩
        pfmap₀ (\p → f (fst (fst p)) (g (snd (fst p)) (snd p))) (fpair₀ (fpair₀ γ α) β)
      ＝⟨⟩
        pfmap₀ (\p → (\b → f (fst (fst p)) (g (snd (fst p)) b)) (snd p)) (fpair₀ (fpair₀ γ α) β)
      ＝⟨⟩
        pfmap₀ ((\p → (fst p) (snd p)) ∘ (\p → ( (\b → f (fst (fst p)) (g (snd (fst p)) b)) , (snd p)))) (fpair₀ (fpair₀ γ α) β)
      ＝⟨ PFmap-Composition' pfunctor _ ⟩
        pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\p → ( (\b → f (fst (fst p)) (g (snd (fst p)) b)) , (snd p))) (fpair₀ (fpair₀ γ α) β))
      ＝⟨⟩
        pfmap₀ (\p → (fst p) (snd p)) (pfmap₀ (\p → ( (\q → (\b → f (fst q) (g (snd q) b))) (fst p) , (snd p))) (fpair₀ (fpair₀ γ α) β))
      ＝⟨- fun-eq (\x → pfmap₀ (\p → fst p (snd p)) x) (Fpair-Fmap-Composition1 pfunctor _ _ _) ⟩
        pfmap₀ (\p → (fst p) (snd p)) (fpair₀ (pfmap₀ (\p → (\b → f (fst p) (g (snd p) b))) (fpair₀ γ α)) β)
      ＝⟨⟩
        pfmap₀ (\p → id (B → E) (fst p) (snd p)) (fpair₀ (pfmap₀ (\p → (\c a b → f c (g a b)) (fst p) (snd p)) (fpair₀ γ α)) β)
      ＝⟨⟩
        liftA2₀ (id (B → E)) (liftA2₀ (\c a b → f c (g a b)) γ α) β
      ＝-qed
  }
  where
    punit₀ : {A : Set i} → A → F A
    punit₀ = punit pfunctor
    pfmap₀ : {A B : Set i} → (A → B) → F A → F B
    pfmap₀ = pfmap pfunctor
    fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
    fpair₀ = fpair pfunctor
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ {A} = punit₀
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ {A} {B} {C} f α β = pfmap₀ (\p → f (fst p) (snd p)) (fpair₀ α β)
  
