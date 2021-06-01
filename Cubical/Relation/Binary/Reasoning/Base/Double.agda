-- Reasoning with both a strict and non-strict relation.
{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.Base.Double {a ℓ₁ ℓ₂} {A : Type a}
  {_≤_ : RawRel A ℓ₁} {_<_ : RawRel A ℓ₂}
  (≤-isPreorder : IsPreorder _≤_)
  (<-transitive : Transitive _<_) (<⇒≤ : _<_ ⇒ _≤_)
  (<-≤-transitive : Trans _<_ _≤_ _<_) (≤-<-transitive : Trans _≤_ _<_ _<_)
  where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Prod using (proj₁; proj₂)
open import Cubical.Foundations.Function using (case_of_; id)
open import Cubical.Relation.Nullary using (Dec; yes; no; IsYes; toWitness)

open IsPreorder ≤-isPreorder
  renaming
  ( reflexive  to ≤-reflexive
  ; transitive to ≤-transitive
  )

------------------------------------------------------------------------
-- A datatype to abstract over the current relation

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Type (ℓ-max a (ℓ-max ℓ₁ ℓ₂)) where
  strict    : (x<y : x < y) → x IsRelatedTo y
  nonstrict : (x≤y : x ≤ y) → x IsRelatedTo y

------------------------------------------------------------------------
-- Types that are used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsStrict {x y} : x IsRelatedTo y → Type (ℓ-max a (ℓ-max ℓ₁ ℓ₂)) where
  isStrict : ∀ x<y → IsStrict (strict x<y)

IsStrict? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsStrict x≲y)
IsStrict? (strict    x<y) = yes (isStrict x<y)
IsStrict? (nonstrict _)   = no λ()

extractStrict : ∀ {x y} {x≲y : x IsRelatedTo y} → IsStrict x≲y → x < y
extractStrict (isStrict x<y) = x<y

------------------------------------------------------------------------
-- Reasoning combinators

infix  0 begin_ begin-strict_
infixr 1 _<⟨_⟩_ _≤⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_ _≡⟨⟩_
infix  2 _∎

-- Beginnings of various types of proofs

begin_ : ∀ {x y} → x IsRelatedTo y → x ≤ y
begin strict    x<y = <⇒≤ x<y
begin nonstrict x≤y = x≤y

begin-strict_ : ∀ {x y} (r : x IsRelatedTo y) → {s : IsYes (IsStrict? r)} → x < y
begin-strict_ r {s} = extractStrict (toWitness s)

-- Step with the strict relation

_<⟨_⟩_ : ∀ (x : A) {y z} → x < y → y IsRelatedTo z → x IsRelatedTo z
x <⟨ x<y ⟩ strict    y<z = strict (<-transitive x<y y<z)
x <⟨ x<y ⟩ nonstrict y≤z = strict (<-≤-transitive x<y y≤z)

-- Step with the non-strict relation

_≤⟨_⟩_ : ∀ (x : A) {y z} → x ≤ y → y IsRelatedTo z → x IsRelatedTo z
x ≤⟨ x≤y ⟩ strict    y<z = strict    (≤-<-transitive x≤y y<z)
x ≤⟨ x≤y ⟩ nonstrict y≤z = nonstrict (≤-transitive x≤y y≤z)

-- Step with non-trivial propositional equality

_≡⟨_⟩_ : ∀ (x : A) {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_≡⟨_⟩_ x {_} {z} x≡y y≲z = J (λ w _ → w IsRelatedTo z) y≲z (sym x≡y)

-- Flipped step with non-trivial propositional equality

_≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
x ≡˘⟨ y≡x ⟩ y≲z = x ≡⟨ sym y≡x ⟩ y≲z

-- Step with trivial propositional equality

_≡⟨⟩_ : ∀ (x : A) {y} → x IsRelatedTo y → x IsRelatedTo y
x ≡⟨⟩ x≲y = x≲y

-- Syntax for path definition

≡⟨⟩-syntax : ∀ x {y z : A} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
≡⟨⟩-syntax = _≡⟨_⟩_
infixr 1 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

≡˘⟨⟩-syntax : ∀ x {y z : A} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
≡˘⟨⟩-syntax = _≡˘⟨_⟩_
infixr 1 ≡˘⟨⟩-syntax
syntax ≡˘⟨⟩-syntax x (λ i → B) y = x ≡˘[ i ]⟨ B ⟩ y

-- Termination step

_∎ : ∀ x → x IsRelatedTo x
x ∎ = nonstrict ≤-reflexive
