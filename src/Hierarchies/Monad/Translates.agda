{-# OPTIONS --prop #-}

module Hierarchies.Monad.Translates where

open import Agda.Primitive
open import Logic
open import Elements
open import TypeClassDefs

Monad-to-Functor : {i : Level} → {F : Set i → Set i} → Monad F → Functor F
Monad-to-Functor {i} {F} monad
  = record {
    fmap = fmap₀
    ; Fmap-Identity = \{A} → fun-ext _ _ (\(α : F A) →
      ＝-begin
        fmap₀ (id A) α
      ＝⟨⟩
        bind₀ α (\a → return₀ ((id A) a))
      ＝⟨⟩
        bind₀ α return₀
      ＝⟨ Return-Right-Identity monad α ⟩
        α
      ＝⟨⟩
        id (F A) α
      ＝-qed
    )
    ; Fmap-Composition = \{A} {B} {C} → \{f : B → C} → \{g : A → B} → fun-ext _ _ (\(α : F A) →
      ＝-begin
        fmap₀ (f ∘ g) α
      ＝⟨⟩
        bind₀ α (\a → return₀ (f (g a)))
      ＝⟨- fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → bind₀ (return₀ (g a)) (\b → return₀ (f b)))
      ＝⟨- Bind-Composition monad _ _ α ⟩
        bind₀ (bind₀ α (\a → return₀ (g a))) (\b → return₀ (f b))
      ＝⟨⟩
        (fmap₀ f) (fmap₀ g α)
      ＝⟨⟩
        ((fmap₀ f) ∘ (fmap₀ g)) α
      ＝-qed
    )
  } where
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    fmap₀ : {A B : Set i} → (A → B) → F A → F B
    fmap₀ f α = bind₀ α (\a → return₀ (f a))

Monad-to-FunctorWithUnit : {i : Level} → {F : Set i → Set i} → Monad F → FunctorWithUnit F
Monad-to-FunctorWithUnit {i} {F} monad
  = record {
    FunctorWithUnit-to-Functor = Monad-to-Functor monad
    ; unit = return₀
    ; Unit-Homomorphism = \{A} {B} → \(a : A) → \(f : A → B) →
      ＝-begin
        fmap₀ f (return₀ a)
      ＝⟨⟩
        bind₀ (return₀ a) (\a' → return₀ (f a'))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        return₀ (f a)
      ＝-qed
  } where
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    functor : Functor F
    functor = Monad-to-Functor monad
    fmap₀ : {A B : Set i} → (A → B) → F A → F B
    fmap₀ = fmap functor

Monad-to-ProductiveFunctor : {i : Level} → {F : Set i → Set i} → Monad F → ProductiveFunctor F
Monad-to-ProductiveFunctor {i} {F} monad
  = record {
    ProductiveFunctor-to-FunctorWithUnit = functorWithUnit
    ; fpair = fpair₀
    ; Fpair-Homomorphism1 = \{A B} → \(a : A) → \(β : F B) →
      ＝-begin
        fpair₀ (unit₀ a) β
      ＝⟨⟩
        bind₀ (return₀ a) (\a → bind₀ β (\b → return₀ (a , b)))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ β (\b → return₀ (a , b))
      ＝⟨⟩
        ufmap₀ (\b → (a , b)) β
      ＝-qed
    ; Fpair-Homomorphism2 = \{A} {B} → \(α : F A) → \(b : B) →
      ＝-begin
        fpair₀ α (unit₀ b)
      ＝⟨⟩
        bind₀ α (\a → bind₀ (return₀ b) (\b → return₀ (a , b)))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → return₀ (a , b))
      ＝⟨⟩
        ufmap₀ (\a → (a , b)) α
      ＝-qed
    ; Fpair-Associative = \{A B C} → \(α : F A) → \(β : F B) → \(γ : F C) →
      ＝-begin
        ufmap₀ assoc-Pair (fpair₀ (fpair₀ α β) γ)
      ＝⟨⟩
        bind₀ (fpair₀ (fpair₀ α β) γ) (\p → return₀ (assoc-Pair p))
      ＝⟨⟩
        bind₀ (bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ (a , b)))) (\p → bind₀ γ (\c → return₀ (p , c)))) (\p → return₀ (assoc-Pair p))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ (a , b)))) (\q → bind₀ (bind₀ γ (\c → return₀ (q , c))) (\p → return₀ (assoc-Pair p)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (bind₀ β (\b → return₀ (a , b))) (\q → bind₀ (bind₀ γ (\c → return₀ (q , c))) (\p → return₀ (assoc-Pair p))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a →
        ＝-begin
          bind₀ (bind₀ β (\b → return₀ (a , b))) (\q → bind₀ (bind₀ γ (λ c → return₀ (q , c))) (\p → return₀ (assoc-Pair p)))
        ＝⟨ Bind-Composition monad _ _ _ ⟩
          bind₀ β (\b → bind₀ (return₀ (a , b)) (\q → bind₀ (bind₀ γ (λ c → return₀ (q , c))) (\p → return₀ (assoc-Pair p))))
        ＝⟨ fun-eq (\x → bind₀ β x) (fun-ext _ _ (\b →
          ＝-begin
            bind₀ (return₀ (a , b)) (\q → bind₀ (bind₀ γ (\c → return₀ (q , c))) (\p → return₀ (assoc-Pair p)))
          ＝⟨ Return-Left-Identity monad _ _ ⟩
            bind₀ (bind₀ γ (\c → return₀ ((a , b) , c))) (\p → return₀ (assoc-Pair p))
          ＝⟨ Bind-Composition monad _ _ _ ⟩
            bind₀ γ (\c → bind₀ (return₀ ((a , b) , c)) (\p → return₀ (assoc-Pair p)))
          ＝⟨ fun-eq (\x → bind₀ γ x) (fun-ext _ _ (\c →
            ＝-begin
              bind₀ (return₀ ((a , b) , c)) (\p → return₀ (assoc-Pair p))
            ＝⟨ Return-Left-Identity monad _ _ ⟩
              return₀ (assoc-Pair ((a , b) , c))
            ＝⟨⟩
              return₀ (a , (b , c))
            ＝⟨- Return-Left-Identity monad _ _ ⟩
              bind₀ (return₀ (b , c)) (\p → return₀ (a , p))
            ＝-qed
            )) ⟩
            bind₀ γ (\c → bind₀ (return₀ (b , c)) (\p → return₀ (a , p)))
          ＝⟨- Bind-Composition monad _ _ _ ⟩
            bind₀ (bind₀ γ (\c → return₀ (b , c))) (\p → return₀ (a , p))
          ＝-qed
          )) ⟩
          bind₀ β (\b → bind₀ (bind₀ γ (\c → return₀ (b , c))) (\p → return₀ (a , p)))
        ＝⟨- Bind-Composition monad _ _ _ ⟩
          bind₀ (bind₀ β (\b → bind₀ γ (\c → return₀ (b , c)))) (\p → return₀ (a , p))
        ＝-qed
        )) ⟩
        bind₀ α (\a → bind₀ (bind₀ β (\b → bind₀ γ (\c → return₀ (b , c)))) (\p → return₀ (a , p)))
      ＝⟨⟩
        fpair₀ α (fpair₀ β γ)
      ＝-qed
    ; Fpair-Fmap-Composition = \{A A' B B'} → \(f : A → A') → \(g : B → B') → \(α : F A) → \(β : F B) →
      ＝-begin
        fpair₀ (ufmap₀ f α) (ufmap₀ g β)
      ＝⟨⟩
        bind₀ (bind₀ α (\a → return₀ (f a))) (\a → bind₀ (bind₀ β (\b → return₀ (g b))) (\b → return₀ (a , b)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (return₀ (f a)) (\a' → bind₀ (bind₀ β (\b → return₀ (g b))) (\b → return₀ (a' , b))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a →
          ＝-begin
            bind₀ (return₀ (f a)) (\a' → bind₀ (bind₀ β (\b → return₀ (g b))) (\b → return₀ (a' , b)))
          ＝⟨ Return-Left-Identity monad _ _ ⟩
            bind₀ (bind₀ β (\b → return₀ (g b))) (\b → return₀ (f a , b))
          ＝⟨ Bind-Composition monad _ _ _ ⟩
            bind₀ β (\b' → bind₀ (return₀ (g b')) (\b → return₀ (f a , b)))
          ＝⟨ fun-eq (\x → bind₀ β x) (fun-ext _ _ (\b →
              ＝-begin
                bind₀ (return₀ (g b)) (\b' → return₀ (f a , b'))
              ＝⟨ Return-Left-Identity monad _ _ ⟩
                return₀ (f a , g b)
              ＝⟨⟩
                return₀ (f (fst (a , b)) , g (snd (a , b)))
              ＝⟨- Return-Left-Identity monad _ _ ⟩
                bind₀ (return₀ (a , b)) (\p → return₀ (f (fst p) , g (snd p)))
              ＝-qed
          )) ⟩
            bind₀ β (\b → bind₀ (return₀ (a , b)) (\p → return₀ (f (fst p) , g (snd p))))
          ＝⟨- Bind-Composition monad _ _ _ ⟩
            bind₀ (bind₀ β (\b → return₀ (a , b))) (\p → return₀ (f (fst p) , g (snd p)))
          ＝-qed
        )) ⟩
        bind₀ α (\a → bind₀ (bind₀ β (\b → return₀ (a , b))) (\p → return₀ (f (fst p) , g (snd p))))
      ＝⟨- Bind-Composition monad _ _ _ ⟩
        bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ (a , b)))) (\p → return₀ (f (fst p) , g (snd p)))
      ＝⟨⟩
        ufmap₀ (\p → (f (fst p) , g (snd p))) (fpair₀ α β)
      ＝-qed
  } where
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    functorWithUnit : FunctorWithUnit F
    functorWithUnit = Monad-to-FunctorWithUnit monad
    fpair₀ : {A B : Set i} → F A → F B → F (Pair A B)
    fpair₀ α β = bind₀ α (\a → bind₀ β (\b → return₀ (a , b)))
    ufmap₀ : {A B : Set i} → (A → B) → F A → F B
    ufmap₀ = ufmap functorWithUnit
    unit₀ : {A : Set i} → A → F A
    unit₀ = unit functorWithUnit
    
Monad-to-Applicative : {i : Level} → {F : Set i → Set i} → Monad F → Applicative F
Monad-to-Applicative {i} {F} monad
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
  
Monad-to-LiftA02 : {i : Level} → {F : Set i → Set i} → Monad F → LiftA02 F
Monad-to-LiftA02 {i} {F} monad
  = record {
    liftA0 = liftA0₀
    ; liftA2 = liftA2₀
    ; LiftA2-Identity = \{A} → fun-ext _ _ (\α →
        ＝-begin
          liftA2₀ (id (A → A)) (liftA0₀ (id A)) α
        ＝⟨⟩
          bind₀ (return₀ (id A)) (\f → bind₀ α (\a → return₀ ((id (A → A)) f a)))
        ＝⟨ Return-Left-Identity monad _ _ ⟩
          bind₀ α (\a → return₀ ((id (A → A)) (id A) a))
        ＝⟨⟩
          bind₀ α return₀
        ＝⟨ Return-Right-Identity monad _ ⟩
          α
        ＝⟨⟩
          id (F A) α
        ＝-qed
      )
    ; LiftA2-Homomorphism = \{A B C} → \(f : A → B → C) → \(a : A) → \(b : B) →
      ＝-begin
        liftA2₀ f (liftA0₀ a) (liftA0₀ b)
      ＝⟨⟩
        bind₀ (return₀ a) (\a' → bind₀ (return₀ b) (\b' → return₀ (f a' b')))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ (return₀ b) (\b' → return₀ (f a b'))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        return₀ (f a b)
      ＝⟨⟩
        liftA0₀ (f a b)
      ＝-qed
    ; LiftA2-Homomorphism2 = \{A B C} → \(f : A → B → C) → \(α : F A) → \(b : B) →
      ＝-begin
        liftA2₀ f α (liftA0₀ b)
      ＝⟨⟩
        bind₀ α (\a → bind₀ (return₀ b) (\b' → return₀ (f a b')))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → return₀ (f a b))
      ＝⟨⟩
        bind₀ α (\a → return₀ ((id (A → C)) (\a → f a b) a))
      ＝⟨- Return-Left-Identity monad _ _ ⟩
        bind₀ (return₀ (\a → f a b)) (\f → bind₀ α (\a → return₀ ((id (A → C)) f a)))
      ＝⟨⟩
        liftA2₀ (id (A → C)) (liftA0₀ (\a → f a b)) α
      ＝-qed
    ; LiftA2-LiftA1-Composition1 = \{A A' B C} → \(f : A' → B → C) → \(g : A → A') → \(α : F A) → \(β : F B) →
      ＝-begin
        liftA2₀ f (liftA2₀ (id (A → A')) (liftA0₀ g) α) β
      ＝⟨⟩
        bind₀ (bind₀ (return₀ g) (\g' → bind₀ α (\a → return₀ (g' a)))) (\a → bind₀ β (\b → return₀ (f a b)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ (return₀ g) (\g' → bind₀ (bind₀ α (\a → return₀ (g' a))) (\a → bind₀ β (\b → return₀ (f a b))))
      ＝⟨ Return-Left-Identity monad _ _ ⟩
        bind₀ (bind₀ α (\a → return₀ (g a))) (\a → bind₀ β (\b → return₀ (f a b)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (return₀ (g a)) (\a' → bind₀ β (\b → return₀ (f a' b))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a → Return-Left-Identity monad _ _)) ⟩
        bind₀ α (\a → bind₀ β (\b → return₀ (f (g a) b)))
      ＝⟨⟩
        liftA2₀ (\a → f (g a)) α β
      ＝-qed
    ; LiftA2-LiftA2-Composition1 = \{A B C D E} → \(f : C → D → E) → \(g : A → B → C) → \(α : F A) → \(β : F B) → \(δ : F D) →
      ＝-begin
        liftA2₀ f (liftA2₀ g α β) δ
      ＝⟨⟩
        bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ (g a b)))) (\c → bind₀ δ (\d → return₀ ((f c) d)))
      ＝⟨ Bind-Composition monad _ _ _ ⟩
        bind₀ α (\a → bind₀ (bind₀ β (\b → return₀ (g a b))) (\c → bind₀ δ (\d → return₀ ((f c) d))))
      ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a →
          ＝-begin
            bind₀ (bind₀ β (\b → return₀ (g a b))) (\c → bind₀ δ (\d → return₀ ((f c) d)))
          ＝⟨ Bind-Composition monad _ _ _ ⟩
            bind₀ β (\b → bind₀ (return₀ (g a b)) (\c → bind₀ δ (\d → return₀ ((f c) d))))
          ＝⟨ fun-eq (\x → bind₀ β x) (fun-ext _ _ (\b →
              ＝-begin
                bind₀ (return₀ (g a b)) (\c → bind₀ δ (\d → return₀ ((f c) d)))
              ＝⟨ Return-Left-Identity monad _ _ ⟩
                bind₀ δ (\d → return₀ ((f (g a b)) d))
              ＝⟨⟩
                bind₀ δ (\d → return₀ (((\a b → f (g a b)) a b) d))
              ＝⟨- Return-Left-Identity monad _ _ ⟩
                bind₀ (return₀ ((\a b → f (g a b)) a b)) (\r → bind₀ δ (\d → return₀ (r d)))
              ＝-qed
            )) ⟩
            bind₀ β (\b → bind₀ (return₀ ((\a b → f (g a b)) a b)) (\r → bind₀ δ (\d → return₀ (r d))))
          ＝⟨- Bind-Composition monad _ _ _ ⟩
            bind₀ (bind₀ β (\b → return₀ ((\a b → f (g a b)) a b))) (\r → bind₀ δ (\d → return₀ (r d)))
          ＝-qed
        )) ⟩
        bind₀ α (\a → bind₀ (bind₀ β (\b → return₀ ((\a b → f (g a b)) a b))) (\r → bind₀ δ (\d → return₀ (r d))))
      ＝⟨- Bind-Composition monad _ _ _ ⟩
        bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ ((\a b → f (g a b)) a b)))) (\r → bind₀ δ (\d → return₀ (r d)))
      ＝⟨⟩
        liftA2₀ (id (D → E)) (liftA2₀ (\a b → f (g a b)) α β) δ
      ＝-qed
    ; LiftA2-LiftA2-Composition2 = \{A B C D E} → \(f : C → D → E) → \(g : A → B → D) → \(α : F A) → \(β : F B) → \(γ : F C) →
      ＝-begin
        liftA2₀ f γ (liftA2₀ g α β)
      ＝⟨⟩
        bind₀ γ (\c → bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ (g a b)))) (\d → return₀ (f c d)))
      ＝⟨ fun-eq (\x → bind₀ γ x) (fun-ext _ _ (\c →
          ＝-begin
            bind₀ (bind₀ α (\a → bind₀ β (\b → return₀ (g a b)))) (\d → return₀ (f c d))
          ＝⟨ Bind-Composition monad _ _ _ ⟩
            bind₀ α (\a → bind₀ (bind₀ β (\b → return₀ (g a b))) (\d → return₀ (f c d)))
          ＝⟨ fun-eq (\x → bind₀ α x) (fun-ext _ _ (\a →
              ＝-begin
                bind₀ (bind₀ β (\b → return₀ (g a b))) (\d → return₀ (f c d))
              ＝⟨ Bind-Composition monad _ _ _ ⟩
                bind₀ β (\b → bind₀ (return₀ (g a b)) (\d → return₀ (f c d)))
              ＝⟨ fun-eq (\x → bind₀ β x) (fun-ext _ _ (\b → Return-Left-Identity monad _ _)) ⟩
                bind₀ β (\b → return₀ ((\b → f c (g a b)) b))
              ＝⟨- Return-Left-Identity monad _ _ ⟩
                bind₀ (return₀ (\b → f c (g a b))) (\r → bind₀ β (\b → return₀ (r b)))
              ＝-qed
            )) ⟩
            bind₀ α (\a → bind₀ (return₀ (\b → f c (g a b))) (\r → bind₀ β (\b → return₀ (r b))))
          ＝⟨- Bind-Composition monad _ _ _ ⟩
            bind₀ (bind₀ α (\a → return₀ (\b → f c (g a b)))) (\r → bind₀ β (\b → return₀ (r b)))
          ＝-qed
        )) ⟩
        bind₀ γ (\c → bind₀ (bind₀ α (\a → return₀ ((\c a b → f c (g a b)) c a))) (\r → bind₀ β (\b → return₀ (r b))))
      ＝⟨- Bind-Composition monad _ _ _ ⟩
        bind₀ (bind₀ γ (\c → bind₀ α (\a → return₀ ((\c a b → f c (g a b)) c a)))) (\r → bind₀ β (\b → return₀ (r b)))
      ＝⟨⟩
        liftA2₀ (id (B → E)) (liftA2₀ (\c a b → f c (g a b)) γ α) β
      ＝-qed
  } where
    return₀ : {A : Set i} → A → F A
    return₀ = return monad
    bind₀ : {A B : Set i} → F A → (A → F B) → F B
    bind₀ = bind monad
    liftA0₀ : {A : Set i} → A → F A
    liftA0₀ = return monad
    liftA2₀ : {A B C : Set i} → (A → B → C) → F A → F B → F C
    liftA2₀ f α β = bind₀ α (\a → bind₀ β (\b → return₀ (f a b)))


