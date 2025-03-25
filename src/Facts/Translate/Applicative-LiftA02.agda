{-# OPTIONS --prop #-}

module Facts.Translate.Applicative-LiftA02 where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs

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
    ; LiftA1-to-LiftA2 = \{A} {B} {C} → \(f : A → B → C) → \(α : F A) → \(β : F B) →
      ＝-begin
        liftA2₀ (id (B → C)) (liftA1₀ f α) β
      ＝⟨⟩
        liftA2₀ (id (B → C)) (liftA2₀ (id (A → B → C)) (pure₀ f) α) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (id (B → C))) (ap₀ (ap₀ (pure₀ (id (A → B → C))) (pure₀ f)) α)) β
      ＝⟨ fun-eq (\x → ap₀ (ap₀ (pure₀ (id (B → C))) (ap₀ x α)) β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (id (B → C))) (ap₀ (pure₀ ((id (A → B → C)) f)) α)) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (id (B → C))) (ap₀ (pure₀ f) α)) β
      ＝⟨ fun-eq (\x → ap₀ (x (ap₀ (pure₀ f) α)) β) (Ap-Identity applicative) ⟩
        ap₀ ((id (F (B → C))) (ap₀ (pure₀ f) α)) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) α) β
      ＝⟨⟩
        liftA2₀ f α β
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
    ; LiftA2-Homomorphism-Left = \{A} {B} {C} → \(f : A → B → C) → \(a : A) → \(β : F B) →
      ＝-begin
        liftA2₀ f (liftA0₀ a) β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) (pure₀ a)) β
      ＝⟨ fun-eq (\x → ap₀ x β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (pure₀ (f a)) β
      ＝⟨⟩
        ap₀ (pure₀ ((id (B → C)) (f a))) β
      ＝⟨- fun-eq (\x → ap₀ x β) (Ap-Homomorphism applicative _ _) ⟩
        ap₀ (ap₀ (pure₀ (id (B → C))) (pure₀ (f a))) β
      ＝⟨⟩
        liftA2₀ (id (B → C)) (liftA0₀ (f a)) β
      ＝⟨⟩
        liftA1₀ (f a) β
      ＝⟨⟩
        liftA1₀ (\b → f a b) β
      ＝-qed
    ; LiftA2-Homomorphism-Right = \{A} {B} {C} → \(f : A → B → C) → \(α : F A) → \(b : B) →
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
        ＝⟨ fun-eq (\x → ap₀ (ap₀ x v) w) (LiftA2-Homomorphism-Left lifta02 _ _ _) ⟩
          ap₀ (ap₀ (liftA1₀ (\f → (id ((B → C) → (A → B) → (A → C))) _∘_ f) u) v) w
        ＝⟨⟩
          ap₀ (ap₀ (liftA1₀ _∘_ u) v) w
        ＝⟨⟩
          ap₀ (liftA2₀ (id ((A → B) → (A → C))) (liftA1₀ _∘_ u) v) w
        ＝⟨ fun-eq (\x → ap₀ x w) (LiftA1-to-LiftA2 lifta02 _ _ _) ⟩
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
        ＝⟨ LiftA2-Homomorphism-Right lifta02 _ _ _ ⟩
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

retract-LiftA02-to-Applicative : {i : Level} → {F : Set i → Set i} → (applicative : Applicative F) → LiftA02-to-Applicative (Applicative-to-LiftA02 applicative) ＝ applicative
retract-LiftA02-to-Applicative {i} {F} applicative
  = Applicative-Eq
    _
    applicative
    (
      ＝-begin
        pure (LiftA02-to-Applicative (Applicative-to-LiftA02 applicative))
      ＝⟨⟩
        liftA0 (Applicative-to-LiftA02 applicative)
      ＝⟨⟩
        pure applicative
      ＝-qed
    )
    \{A} {B} → fun-ext _ _ (\(ψ : F (A → B)) → fun-ext _ _ (\(α : F A) →
      ＝-begin
        ap (LiftA02-to-Applicative (Applicative-to-LiftA02 applicative)) ψ α
      ＝⟨⟩
        liftA2 (Applicative-to-LiftA02 applicative) (id (A → B)) ψ α
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ (id (A → B))) ψ) α
      ＝⟨ fun-eq (\x → ap₀ (x ψ) α) (Ap-Identity applicative) ⟩
        ap₀ (id (F (A → B)) ψ) α
      ＝⟨⟩
        ap₀ ψ α
      ＝-qed
    ))
    where
      pure₀ : {A : Set i} → A → F A
      pure₀ = pure applicative
      ap₀ : {A B : Set i} → F (A → B) → F A → F B
      ap₀ = ap applicative

retract-Applicative-to-LiftA02 : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → Applicative-to-LiftA02 (LiftA02-to-Applicative lifta02) ＝ lifta02
retract-Applicative-to-LiftA02 {i} {F} lifta02 =
  LiftA02-Eq
    _
    lifta02
    (\{A} → fun-ext _ _ (\(a : A) →
      ＝-begin
        liftA0 (Applicative-to-LiftA02 (LiftA02-to-Applicative lifta02)) a
      ＝⟨⟩
        pure₀ a
      ＝⟨⟩
        liftA0₀ a
      ＝-qed
    ))
    (\{A} {B} {C} → (fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        liftA2 (Applicative-to-LiftA02 (LiftA02-to-Applicative lifta02)) f α β
      ＝⟨⟩
        ap₀ (ap₀ (pure₀ f) α) β
      ＝⟨⟩
        ap₀ (liftA2₀ (id (A → B → C)) (liftA0₀ f) α) β
      ＝⟨⟩
        liftA2₀ (id (B → C)) (liftA2₀ (id (A → B → C)) (liftA0₀ f) α) β
      ＝⟨ fun-eq (\x → liftA2₀ (id (B → C)) x β) (LiftA2-Homomorphism-Left lifta02 _ _ _) ⟩
        liftA2₀ (id (B → C)) (liftA1₀ (\a → id (A → B → C) f a) α) β
      ＝⟨⟩
        liftA2₀ (id (B → C)) (liftA1₀ f α) β
      ＝⟨ LiftA1-to-LiftA2 lifta02 _ _ _ ⟩
        liftA2₀ f α β
      ＝-qed
    )))))
  where
    pure₀ : {A : Set i} → A → F A
    pure₀ = pure (LiftA02-to-Applicative lifta02)
    ap₀ : {A B : Set i} → (F (A → B)) → F A → F B
    ap₀ = ap (LiftA02-to-Applicative lifta02)
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ = liftA0 lifta02
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ = liftA2 lifta02
    liftA1₀ : {A B : Set i} → (A → B) → F A → F B
    liftA1₀ {A} {B} f = liftA2₀ (id (A → B)) (liftA0₀ f)
