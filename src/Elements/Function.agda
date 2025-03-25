module Elements.Function where

open import Agda.Primitive

infixl 300 _∘_
_∘_ : {i : Level} → {A B C : Set i} → (B → C) → (A → B) → (A → C)
_∘_ g f a = g (f a) 

id : {i : Level} → (A : Set i) → A → A
id A a = a

const : {i : Level} → (A  B : Set i) → A → B → A
const A B a b = a

flip : {i : Level} → {A B C : Set i} → (A → B → C) → (B → A → C)
flip f = (\b → \a → f a b)
