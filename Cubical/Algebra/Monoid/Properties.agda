{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Monoid.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Monoid.Morphism

open import Cubical.Algebra.Semigroup.Properties as Semigroup using (isPropIsSemigroup)

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Reasoning.Equality

open import Cubical.Algebra.Monoid.MorphismProperties public
  using (MonoidPath; uaMonoid; carac-uaMonoid; Monoid≡; caracMonoid≡)

private
  variable
    ℓ : Level


isPropIsMonoid : ∀ {M : Type ℓ} {_•_ ε} → isProp (IsMonoid M _•_ ε)
isPropIsMonoid {_} {_} {_•_} {ε} (ismonoid aSemi aId) (ismonoid bSemi bId) =
  cong₂ ismonoid (isPropIsSemigroup aSemi bSemi) (isPropIdentity (IsSemigroup.is-set aSemi) _•_ ε aId bId)


module MonoidLemmas (M : Monoid ℓ) where
  open Monoid M

  ε-comm : ∀ x → x • ε ≡ ε • x
  ε-comm x = identityʳ x ∙ sym (identityˡ x)


  ^-zeroˡ : LeftZero ε _^_
  ^-zeroˡ zero    = refl
  ^-zeroˡ (suc n) = identityˡ (ε ^ n) ∙ ^-zeroˡ n

  ^-suc : ∀ x n → x ^ suc n ≡ x ^ n • x
  ^-suc x zero    = ε-comm x
  ^-suc x (suc n) =
    x ^ suc (suc n) ≡⟨⟩
    x • x ^ suc n   ≡⟨ cong (x •_) (^-suc x n) ⟩
    x • (x ^ n • x) ≡˘⟨ assoc x (x ^ n) x ⟩
    x • x ^ n • x   ≡⟨⟩
    x ^ suc n • x   ∎

  ^-plus : ∀ x → Homomorphic₂ (x ^_) _+_ _•_
  ^-plus x zero    n = sym (identityˡ (x ^ n))
  ^-plus x (suc m) n =
    x ^ (suc m + n)     ≡⟨⟩
    x • x ^ (m + n)     ≡⟨ cong (x •_) (^-plus x m n) ⟩
    x • (x ^ m • x ^ n) ≡˘⟨ assoc x (x ^ m) (x ^ n) ⟩
    x • x ^ m • x ^ n   ≡⟨⟩
    x ^ suc m • x ^ n   ∎

  infixl 10 _^′_
  _^′_ = Semigroup._^_ semigroup

  ^semi≡^ : ∀ x n → x ^′ n ≡ x ^ (ℕ₊₁→ℕ n)
  ^semi≡^ x one    = sym (identityʳ x)
  ^semi≡^ x (2+ n) = cong (x •_) (^semi≡^ x (1+ n))


-- Invertible elements
module Invertible (M : Monoid ℓ) where
  open Monoid M

  Inverses : Rel Carrier ℓ
  Inverses x y = (x • y ≡ ε) × (y • x ≡ ε)

  isPropInverses : isPropValued Inverses
  isPropInverses _ _ = isPropProd (is-set _ _) (is-set _ _)

  Inversesᴿ : PropRel Carrier ℓ
  Inversesᴿ = Inverses , isPropInverses

  inv-unique′ : ∀ {x y z} → x • y ≡ ε → z • x ≡ ε → y ≡ z
  inv-unique′ {x} {y} {z} xy≡ε zx≡ε =
    y           ≡˘⟨ identityˡ y ⟩
    ε • y       ≡˘⟨ cong (_• y) zx≡ε ⟩
    (z • x) • y ≡⟨ assoc z x y ⟩
    z • (x • y) ≡⟨ cong (z •_) xy≡ε ⟩
    z • ε       ≡⟨ identityʳ z ⟩
    z           ∎

  inv-unique : ∀ {x y z} → Inverses x y → Inverses x z → y ≡ z
  inv-unique (xy≡ε , _) (_ , zx≡ε) = inv-unique′ xy≡ε zx≡ε

  Invertible : Carrier → Type ℓ
  Invertible x = Σ Carrier (Inverses x)

  isPropInvertible : ∀ x → isProp (Invertible x)
  isPropInvertible x (y , x-y) (z , x-z) = ΣPathTransport→PathΣ (y , x-y) (z , x-z)
                                          (inv-unique x-y x-z , isPropInverses _ _ _ _)

  εInverses : Inverses ε ε
  εInverses = identityˡ ε , identityˡ ε

  εInvertible : Invertible ε
  εInvertible = ε , εInverses


module Kernel {ℓ ℓ′} {M : Monoid ℓ} {N : Monoid ℓ′} (hom : MonoidHom M N)
  = Semigroup.Kernel (MonoidHom→SemigroupHom hom)


open MonoidLemmas public
open Invertible public
