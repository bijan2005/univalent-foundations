{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Definitions where

open import Cubical.Core.Everything
open import Cubical.Relation.Binary
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥)

open import Cubical.Algebra.Base

private
  variable
    a b c ℓ : Level
    A : Type a
    B : Type b
    C : Type c

------------------------------------------------------------------------
-- Properties of operations

Congruent₁ : Rel A ℓ → Op₁ A → Type _
Congruent₁ R f = f Preserves R ⟶ R

Congruent₂ : Rel A ℓ → Op₂ A → Type _
Congruent₂ R • = • Preserves₂ R ⟶ R ⟶ R

LeftCongruent : Rel A ℓ → Op₂ A → Type _
LeftCongruent R _•_ = ∀ {x} → (x •_) Preserves R ⟶ R

RightCongruent : Rel A ℓ → Op₂ A → Type _
RightCongruent R _•_ = ∀ {x} → (_• x) Preserves R ⟶ R

Homomorphic₀ : (A → B) → A → B → Type _
Homomorphic₀ ⟦_⟧ x y = ⟦ x ⟧ ≡ y

Homomorphic₁ : (A → B) → Op₁ A → Op₁ B → Type _
Homomorphic₁ ⟦_⟧ f g = ∀ x → ⟦ f x ⟧ ≡ g ⟦ x ⟧

Homomorphic₂ : (A → B) → Op₂ A → Op₂ B → Type _
Homomorphic₂ ⟦_⟧ _•_ _◦_ = ∀ x y → ⟦ x • y ⟧ ≡ ⟦ x ⟧ ◦ ⟦ y ⟧

Contramorphic₂ : (A → B) → Op₂ A → Op₂ B → Type _
Contramorphic₂ ⟦_⟧ _•_ _◦_ = ∀ x y → ⟦ x • y ⟧ ≡ ⟦ y ⟧ ◦ ⟦ x ⟧

Associative : Op₂ A → Type _
Associative _•_ = ∀ x y z → (x • y) • z ≡ x • (y • z)

Commutative : Op₂ A → Type _
Commutative _•_ = ∀ x y → x • y ≡ y • x

LeftIdentity : A → Opₗ A B → Type _
LeftIdentity e _•_ = ∀ x → e • x ≡ x

RightIdentity : A → Opᵣ A B → Type _
RightIdentity e _•_ = ∀ x → x • e ≡ x

Identity : A → Op₂ A → Type _
Identity e • = (LeftIdentity e •) × (RightIdentity e •)

LeftZero : A → Opᵣ B A → Type _
LeftZero z _•_ = ∀ x → z • x ≡ z

RightZero : A → Opₗ B A → Type _
RightZero z _•_ = ∀ x → x • z ≡ z

Zero : A → Op₂ A → Type _
Zero z • = (LeftZero z •) × (RightZero z •)

LeftInverse : C → (A → B) → (B → A → C) → Type _
LeftInverse e _⁻¹ _•_ = ∀ x → (x ⁻¹) • x ≡ e

RightInverse : C → (A → B) → (A → B → C) → Type _
RightInverse e _⁻¹ _•_ = ∀ x → x • (x ⁻¹) ≡ e

Inverse : A → Op₁ A → Op₂ A → Type _
Inverse e ⁻¹ • = (LeftInverse e ⁻¹ •) × (RightInverse e ⁻¹ •)

LeftConical : B → Opᵣ A B → Type _
LeftConical e _•_ = ∀ x y → x • y ≡ e → x ≡ e

RightConical : B → Opₗ A B → Type _
RightConical e _•_ = ∀ x y → x • y ≡ e → y ≡ e

Conical : A → Op₂ A → Type _
Conical e • = (LeftConical e •) × (RightConical e •)

_DistributesOverˡ_ : Opₗ A B → Op₂ B → Type _
_*_ DistributesOverˡ _+_ =
  ∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))

_DistributesOverʳ_ : Opᵣ A B → Op₂ B → Type _
_*_ DistributesOverʳ _+_ =
  ∀ x y z → ((y + z) * x) ≡ ((y * x) + (z * x))

_DistributesOver_ : Op₂ A → Op₂ A → Type _
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ A → A → Type _
_•_ IdempotentOn x = (x • x) ≡ x

Idempotent : Op₂ A → Type _
Idempotent • = ∀ x → • IdempotentOn x

IdempotentFun : Op₁ A → Type _
IdempotentFun f = ∀ x → f (f x) ≡ f x

Selective : Op₂ A → Type _
Selective _•_ = ∀ x y → ∥ (x • y ≡ x) ⊎ (x • y ≡ y) ∥

_Absorbs_ : Op₂ A → Op₂ A → Type _
_∧_ Absorbs _∨_ = ∀ x y → (x ∧ (x ∨ y)) ≡ x

Absorptive : Op₂ A → Op₂ A → Type _
Absorptive ∧ ∨ = (∧ Absorbs ∨) × (∨ Absorbs ∧)

Involutive : Op₁ A → Type _
Involutive f = ∀ x → f (f x) ≡ x

LeftCancellative : (A → B → C) → Type _
LeftCancellative _•_ = ∀ x {y z} → (x • y) ≡ (x • z) → y ≡ z

RightCancellative : (A → B → C) → Type _
RightCancellative _•_ = ∀ {x y} z → (x • z) ≡ (y • z) → x ≡ y

Cancellative : (A → A → B) → Type _
Cancellative • = (LeftCancellative •) × (RightCancellative •)

Interchangeable : Op₂ A → Op₂ A → Type _
Interchangeable _•_ _◦_ = ∀ w x y z → ((w • x) ◦ (y • z)) ≡ ((w ◦ y) • (x ◦ z))
