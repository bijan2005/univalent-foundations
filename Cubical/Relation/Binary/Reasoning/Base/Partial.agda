{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.Base.Partial
  {a ℓ} {A : Type a} (_∼_ : RawRel A ℓ) (transitive : Transitive _∼_)
  where

open import Cubical.Foundations.Prelude

infix  4 _IsRelatedTo_

infix  2 _∎⟨_⟩
infixr 1 _∼⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
infixr 1 _≡⟨⟩_
infix  0 begin_

------------------------------------------------------------------------
-- Definition of "related to"

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ (x y : A) : Type ℓ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

------------------------------------------------------------------------
-- Reasoning combinators

-- Beginning of a proof

begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

-- Standard step with the relation

_∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (transitive x∼y y∼z)

-- Step with a non-trivial propositional equality

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_≡⟨_⟩_ x {_} {z} x≡y y∼z = J (λ w _ → w IsRelatedTo z) y∼z (sym x≡y)

-- Step with a flipped non-trivial propositional equality

_≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
x ≡˘⟨ y≡x ⟩ y∼z = x ≡⟨ sym y≡x ⟩ y∼z

-- Step with a trivial propositional equality

_≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≡⟨⟩ x∼y = x∼y

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

_∎⟨_⟩ : ∀ x → x ∼ x → x IsRelatedTo x
_ ∎⟨ x∼x ⟩ = relTo x∼x
