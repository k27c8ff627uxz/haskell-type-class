module Elements.Types.List where

open import Agda.Primitive

infixr 40 _∷_
data List {i} (A : Set i) : Set i where
  nil : List A
  _∷_ : A → List A → List A

list-fmap : {i : Level} → {A B : Set i} → (A → B) → (List A → List B)
list-fmap f nil = nil
list-fmap f (a ∷ la) = f a ∷ list-fmap f la

_⧺_ : {i : Level} → {A : Set i} → List A → List A → List A
nil ⧺ l₂ = l₂
(a ∷ l₁) ⧺ l₂ = a ∷ (l₁ ⧺ l₂)
