{-# OPTIONS --prop #-}

module Elements.Types.TypedList where

open import Agda.Primitive
open import Logic
open import Elements.Types.Pair
open import Elements.Types.List

infixr 40 _t∷_
data TypedList {i} : List (Set i) → Set (lsuc i) where
  tnil : TypedList nil
  _t∷_ : {ltype : List (Set i)} → {A : Set i} → A → TypedList ltype → TypedList (A ∷ ltype)


id-TypedList : {i : Level} → (A : Set i) → TypedList (A ∷ nil) → A
id-TypedList {i} A (a t∷ l) = a

_t++_ : {i : Level} → {typedA typedB : List (Set i)} → TypedList typedA → TypedList typedB → TypedList (typedA ⧺ typedB)
tnil t++ l₂ = l₂
(a t∷ l₁) t++ l₂ = a t∷ (l₁ t++ l₂)

dest-typedlist-element : {i : Level} → {typed : List (Set i)} → {A : Set i} → TypedList (A ∷ typed) → Pair A (TypedList typed)
dest-typedlist-element {i} {typed} {A} (a t∷ l) = (a , l)

dest-typelist : {i : Level} → (typed₁ typed₂ : List (Set i)) → (l : TypedList (typed₁ ⧺ typed₂)) → Pair (TypedList typed₁) (TypedList typed₂)
dest-typelist {i} nil typed₂ l = (tnil , l)
dest-typelist {i} (A ∷ typed₁) typed₂ (a t∷ l') =
  let p : Pair (TypedList typed₁) (TypedList typed₂)
      p = dest-typelist {i} typed₁ typed₂ l'
      in ((a t∷ fst p) , snd p)

dest-typelist-eq : {i : Level} → {typed₁ typed₂ : List (Set i)} → (l₁ : TypedList typed₁) → (l₂ : TypedList typed₂) → dest-typelist typed₁ typed₂ (l₁ t++ l₂) ＝ (l₁ , l₂)
dest-typelist-eq {i} {nil} {typed₂} tnil l₂ = ＝-refl _
dest-typelist-eq {i} {A ∷ typed₁} {typed₂} (a t∷ l₁) l₂ =
  let p : Pair (TypedList typed₁) (TypedList typed₂)
      p = dest-typelist typed₁ typed₂ (l₁ t++ l₂) in
  let p-eq : p ＝ (l₁ , l₂)
      p-eq = dest-typelist-eq l₁ l₂ in
  ＝-begin
    dest-typelist (A ∷ typed₁) typed₂ ((a t∷ l₁) t++ l₂)
  ＝⟨ ＝-refl _ ⟩
    ( (a t∷ fst p) , snd p )
  ＝⟨ fun-eq (\x → (a t∷ fst x) , snd x) p-eq ⟩
    ( (a t∷ l₁) , l₂)
  ＝-qed

composition-TypedList : {i : Level} → {typed₁ typed₂ : List (Set i)} → {A B : Set i} → (f : (TypedList (A ∷ typed₂)) → B) → (g : (TypedList typed₁) → A) → (TypedList (typed₁ ⧺ typed₂)) → B
composition-TypedList {i} {typed₁} {typed₂} {A} {B} f g l =
  let p : Pair (TypedList typed₁) (TypedList typed₂)
      p = dest-typelist typed₁ typed₂ l in
  f (g (fst p) t∷ snd p)


t++-fmap-homomorphism : {i : Level} → {F : Set i → Set i} → (typed₁ typed₂ : List (Set i)) → (TypedList (list-fmap F (typed₁ ⧺ typed₂))) → (TypedList ((list-fmap F typed₁) ⧺ (list-fmap F typed₂)))
t++-fmap-homomorphism {i} {F} nil typed₂ l = l
t++-fmap-homomorphism {i} {F} (A ∷ typed₁) typed₂ (fa t∷ l) =
  let v : TypedList ((list-fmap F typed₁) ⧺ (list-fmap F typed₂))
      v = t++-fmap-homomorphism typed₁ typed₂ l in
  fa t∷ v

fmap-t++-homomorphism : {i : Level} → {F : Set i → Set i} → (typed₁ typed₂ : List (Set i)) → (TypedList ((list-fmap F typed₁) ⧺ (list-fmap F typed₂))) → (TypedList (list-fmap F (typed₁ ⧺ typed₂)))
fmap-t++-homomorphism {i} {F} nil typed₂ l = l
fmap-t++-homomorphism {i} {F} (A ∷ typed₁) typed₂ (fa t∷ l) =
  let v : TypedList (list-fmap F (typed₁ ⧺ typed₂))
      v = fmap-t++-homomorphism typed₁ typed₂ l in
  fa t∷ v
