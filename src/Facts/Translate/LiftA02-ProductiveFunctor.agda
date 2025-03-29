{-# OPTIONS --prop #-}

module Facts.Translate.LiftA02-ProductiveFunctor where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs
open import Facts.Translate.Applicative-Functor
open import Facts.Translate.Applicative-FunctorWithUnit
open import Facts.Translate.Applicative-LiftA02

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

LiftA02-to-ProductiveFunctor-punit-eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → {A : Set i} → punit (LiftA02-to-ProductiveFunctor lifta02) {A} ＝ liftA0 lifta02 {A}
LiftA02-to-ProductiveFunctor-punit-eq {i} {F} lifta02 {A} = ＝-refl _

LiftA02-to-ProductiveFunctor-pfmap-eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → {A B : Set i} → pfmap (LiftA02-to-ProductiveFunctor lifta02) {A} {B} ＝ ufmap (LiftA02-to-FunctorWithUnit lifta02) {A} {B}
LiftA02-to-ProductiveFunctor-pfmap-eq {i} {F} lifta02 {A} {B} = ＝-refl _

LiftA02-to-ProductiveFunctor-fpair-eq : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → {A B : Set i} → fpair (LiftA02-to-ProductiveFunctor lifta02) {A} {B} ＝ liftA2 lifta02 {A} {B} (\a → \b → (a , b))
LiftA02-to-ProductiveFunctor-fpair-eq {i} {F} lifta02 {A} {B} = ＝-refl _

ProductiveFunctor-to-LiftA02-liftA2-eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → {A B C : Set i} → (f : A → B → C) → (α : F A) → (β : F B) → liftA2 (ProductiveFunctor-to-LiftA02 pfunctor) f α β ＝ pfmap pfunctor (\p → f (fst p) (snd p)) (fpair pfunctor α β)
ProductiveFunctor-to-LiftA02-liftA2-eq {i} {F} pfunctor {A} {B} {C} f α β = ＝-refl _

ProductiveFunctor-to-LiftA02-liftA0-eq : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → {A : Set i} → liftA0 (ProductiveFunctor-to-LiftA02 pfunctor) {A} ＝ punit pfunctor {A}
ProductiveFunctor-to-LiftA02-liftA0-eq {i} {F} pfunctor {A} = ＝-refl _

ProductiveFunctor-to-LiftA02-liftA1-eq-pfmap : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → {A B : Set i} → liftA1 (ProductiveFunctor-to-LiftA02 pfunctor) {A} {B} ＝ pfmap pfunctor {A} {B}
ProductiveFunctor-to-LiftA02-liftA1-eq-pfmap {i} {F} pfunctor {A} {B} = fun-ext _ _ (\(f : A → B) → fun-ext _ _ (\(α : F A) →
  ＝-begin
    liftA1 (ProductiveFunctor-to-LiftA02 pfunctor) f α
  ＝⟨⟩
    liftA2 (ProductiveFunctor-to-LiftA02 pfunctor) (id (A → B)) (liftA0 (ProductiveFunctor-to-LiftA02 pfunctor) f) α
  ＝⟨⟩
    pfmap pfunctor (\p → (id (A → B)) (fst p) (snd p)) (fpair pfunctor (punit pfunctor f) α)
  ＝⟨⟩
    pfmap pfunctor (\p → (fst p) (snd p)) (fpair pfunctor (punit pfunctor f) α)
  ＝⟨ fun-eq (\x → pfmap pfunctor (\p → fst p (snd p)) x) (Fpair-Homomorphism1 pfunctor f α) ⟩
    pfmap pfunctor (\p → (fst p) (snd p)) (pfmap pfunctor (\b → (f , b)) α)
  ＝⟨- PFmap-Composition' pfunctor α ⟩
    pfmap pfunctor ((\p → (fst p) (snd p)) ∘ (\b → (f , b))) α
  ＝⟨⟩
    pfmap pfunctor f α
  ＝-qed
  ))

retract-LiftA02-to-ProductiveFunctor : {i : Level} → {F : Set i → Set i} → (pfunctor : ProductiveFunctor F) → LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor) ＝ pfunctor
retract-LiftA02-to-ProductiveFunctor {i} {F} pfunctor
  = ProductiveFunctor-Eq
    _
    pfunctor
    (
      FunctorWithUnit-Eq
        _
        _
        (
          Functor-Equal
          _ _
          (\A B →
            ＝-begin
              fmap (FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor))))
            ＝⟨⟩
              ufmap (ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor)))
            ＝⟨⟩
              pfmap (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor))
            ＝⟨⟩
              ufmap (LiftA02-to-FunctorWithUnit (ProductiveFunctor-to-LiftA02 pfunctor))
            ＝⟨⟩
              fmap (LiftA02-to-Functor (ProductiveFunctor-to-LiftA02 pfunctor))
            ＝⟨⟩
              liftA1 (ProductiveFunctor-to-LiftA02 pfunctor)
            ＝⟨ ProductiveFunctor-to-LiftA02-liftA1-eq-pfmap pfunctor ⟩
              pfmap pfunctor
            ＝⟨⟩
              ufmap (ProductiveFunctor-to-FunctorWithUnit pfunctor)
            ＝⟨⟩
              fmap (FunctorWithUnit-to-Functor (ProductiveFunctor-to-FunctorWithUnit pfunctor))
            ＝-qed
          )
        )
        (\{A} →
          ＝-begin
            unit (ProductiveFunctor-to-FunctorWithUnit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor)))
          ＝⟨⟩
            punit (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor))
          ＝⟨⟩
            liftA0 (ProductiveFunctor-to-LiftA02 pfunctor)
          ＝⟨⟩
            punit pfunctor
          ＝⟨⟩
            unit (ProductiveFunctor-to-FunctorWithUnit pfunctor)
          ＝-qed
        )
    )
    (\A B → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        fpair (LiftA02-to-ProductiveFunctor (ProductiveFunctor-to-LiftA02 pfunctor)) α β
      ＝⟨⟩
        liftA2 (ProductiveFunctor-to-LiftA02 pfunctor) (\a → \b → (a , b)) α β
      ＝⟨⟩
        pfmap pfunctor (\p → (\a → \b → (a , b)) (fst p) (snd p)) (fpair pfunctor α β)
      ＝⟨⟩
        pfmap pfunctor (id (Pair A B)) (fpair pfunctor α β)
      ＝⟨ fun-eq (\x → x (fpair pfunctor α β)) (PFmap-Identity pfunctor) ⟩
        (id (F (Pair A B))) (fpair pfunctor α β)
      ＝⟨⟩
        fpair pfunctor α β
      ＝-qed
    )))

retract-ProductiveFunctor-to-LiftA02 : {i : Level} → {F : Set i → Set i} → (lifta02 : LiftA02 F) → ProductiveFunctor-to-LiftA02 (LiftA02-to-ProductiveFunctor lifta02) ＝ lifta02
retract-ProductiveFunctor-to-LiftA02 {i} {F} lifta02 =
  LiftA02-Eq
    _ lifta02
    (\{A} →
      ＝-begin
        liftA0 (ProductiveFunctor-to-LiftA02 (LiftA02-to-ProductiveFunctor lifta02))
      ＝⟨⟩
        punit (LiftA02-to-ProductiveFunctor lifta02)
      ＝⟨⟩
        liftA0 lifta02
      ＝-qed
    )
    (\{A} {B} {C} → fun-ext _ _ (\(f : A → B → C) → fun-ext _ _ (\(α : F A) → fun-ext _ _ (\(β : F B) →
      ＝-begin
        liftA2 (ProductiveFunctor-to-LiftA02 (LiftA02-to-ProductiveFunctor lifta02)) f α β
      ＝⟨⟩
        pfmap (LiftA02-to-ProductiveFunctor lifta02) (\p → f (fst p) (snd p)) (fpair (LiftA02-to-ProductiveFunctor lifta02) α β)
      ＝⟨⟩
        ufmap (LiftA02-to-FunctorWithUnit lifta02) (\p → f (fst p) (snd p)) (liftA2 lifta02 (\a → \b → (a , b)) α β)
      ＝⟨⟩
        fmap (LiftA02-to-Functor lifta02) (\p → f (fst p) (snd p)) (liftA2 lifta02 (\a → \b → (a , b)) α β)
      ＝⟨⟩
        liftA1 lifta02 (\p → f (fst p) (snd p)) (liftA2 lifta02 (\a → \b → (a , b)) α β)
      ＝⟨ LiftA1-LiftA2-Composition lifta02 _ _ _ _ ⟩
        liftA2 lifta02 (\a → \b → (\p → f (fst p) (snd p)) ((\a' → \b' → (a' , b')) a b)) α β
      ＝⟨⟩
        liftA2 lifta02 f α β
      ＝-qed
    ))))
