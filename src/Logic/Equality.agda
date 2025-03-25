
{-# OPTIONS --prop #-}

module Logic.Equality where

open import Agda.Primitive

infix 80 _＝_

data _＝_ {i} {A : Set i} : A → A → Prop i where
  ＝-refl : (a : A) → a ＝ a

＝-sym : {i : Level} → {A : Set i} → (x y : A) → x ＝ y → y ＝ x
＝-sym x x (＝-refl x) = ＝-refl x

＝-trans : {i : Level} → {A : Set i} → (x y z : A) → x ＝ y → y ＝ z → x ＝ z
＝-trans x x x (＝-refl x) (＝-refl x) = ＝-refl x

＝-rewrite : {i j : Level} → {A : Set i} → {x y : A} → (P : A → Prop j) → (eqxy : x ＝ y) → P x → P y
＝-rewrite {i} {j} {A} {x} {x} P (＝-refl x) Px = Px

module ＝-Reasoning {i : Level} {A : Set i} where

  infix  1 ＝-begin_
  infixr 2 step-＝-∣ step-＝-⟩ step-＝⟨-
  infix  3 _＝-qed

  ＝-begin_ : ∀ {x y : A} → x ＝ y → x ＝ y
  ＝-begin eqxy  =  eqxy

  step-＝-∣ : ∀ (x : A) {y : A} → x ＝ y → x ＝ y
  step-＝-∣ x eqxy =  eqxy

  step-＝-⟩ : ∀ (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
  step-＝-⟩ x {y} {z} eqyz eqxy  =  ＝-trans x y z eqxy eqyz

  step-＝⟨- : ∀ (x : A) {y z : A} → y ＝ z → y ＝ x → x ＝ z
  step-＝⟨- x {y} {z} eqyz eqyx = step-＝-⟩ x eqyz (＝-sym y x eqyx)

  syntax step-＝-∣ x eqxy      =  x ＝⟨⟩ eqxy
  syntax step-＝-⟩ x eqyz eqxy  =  x ＝⟨ eqxy ⟩ eqyz
  syntax step-＝⟨- x eqyz eqyx = x ＝⟨- eqyx ⟩ eqyz

  _＝-qed : ∀ (x : A) → x ＝ x
  x ＝-qed  =  ＝-refl x


  ＝-confluence : ∀ {x y a : A} → x ＝ a → y ＝ a → x ＝ y
  ＝-confluence {x} {y} {a} eqxa eqya = ＝-trans x a y eqxa (＝-sym y a eqya)

open ＝-Reasoning public
