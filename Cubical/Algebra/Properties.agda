{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything

module Cubical.Algebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Binary.Base using (Rel)
open import Cubical.Relation.Binary.Definitions

open import Cubical.Algebra.Base
open import Cubical.Algebra.Definitions
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Binary.Reasoning.Equality

private
  variable
    ℓ : Level
    A : Type ℓ

----------------------------------------------------------------------
-- Operation properties are propositions


private
  isPropImpΠ2 : ∀ {ℓ′ ℓ′′} {B : A → Type ℓ′} {C : ∀ x → B x → Type ℓ′′} →
                  (∀ x y → isProp (C x y)) → isProp (∀ {x y} → C x y)
  isPropImpΠ2 isPropC f g i {x} {y} = isPropC x y (f {x} {y}) (g {x} {y}) i

module _ (isSetA : isSet A) where

  isPropAssociative : (_•_ : Op₂ A) → isProp (Associative _•_)
  isPropAssociative _ = isPropΠ3 λ _ _ _ → isSetA _ _

  isPropCommutative : (_•_ : Op₂ A) → isProp (Commutative _•_)
  isPropCommutative _ = isPropΠ2 λ _ _ → isSetA _ _

  isPropLeftIdentity : (_•_ : Op₂ A) (e : A) → isProp (LeftIdentity e _•_)
  isPropLeftIdentity _ _ = isPropΠ λ _ → isSetA _ _

  isPropRightIdentity : (_•_ : Op₂ A) (e : A) → isProp (RightIdentity e _•_)
  isPropRightIdentity _ _ = isPropΠ λ _ → isSetA _ _

  isPropIdentity : (_•_ : Op₂ A) (e : A) → isProp (Identity e _•_)
  isPropIdentity _•_ e = isProp× (isPropLeftIdentity _•_ e) (isPropRightIdentity _•_ e)

  isPropLeftZero : (_•_ : Op₂ A) (z : A) → isProp (LeftZero z _•_)
  isPropLeftZero _ _ = isPropΠ λ _ → isSetA _ _

  isPropRightZero : (_•_ : Op₂ A) (z : A) → isProp (RightZero z _•_)
  isPropRightZero _ _ = isPropΠ λ _ → isSetA _ _

  isPropZero : (_•_ : Op₂ A) (z : A) → isProp (Zero z _•_)
  isPropZero _•_ z = isProp× (isPropLeftZero _•_ z) (isPropRightZero _•_ z)

  isPropLeftInverse : (_•_ : Op₂ A) (_⁻¹ : Op₁ A) (e : A) → isProp (LeftInverse e _⁻¹ _•_)
  isPropLeftInverse _ _ _ = isPropΠ λ _ → isSetA _ _

  isPropRightInverse : (_•_ : Op₂ A) (_⁻¹ : Op₁ A) (e : A) → isProp (RightInverse e _⁻¹ _•_)
  isPropRightInverse _ _ _ = isPropΠ λ _ → isSetA _ _

  isPropInverse : (_•_ : Op₂ A) (_⁻¹ : Op₁ A) (e : A) → isProp (Inverse e _⁻¹ _•_)
  isPropInverse _•_ _⁻¹ e = isProp× (isPropLeftInverse _•_ _⁻¹ e) (isPropRightInverse _•_ _⁻¹ e)

  isPropLeftConical : (_•_ : Op₂ A) (e : A) → isProp (LeftConical e _•_)
  isPropLeftConical _ _ = isPropΠ3 λ _ _ _ → isSetA _ _

  isPropRightConical : (_•_ : Op₂ A) (e : A) → isProp (RightConical e _•_)
  isPropRightConical _ _ = isPropΠ3 λ _ _ _ → isSetA _ _

  isPropConical : (_•_ : Op₂ A) (e : A) → isProp (Conical e _•_)
  isPropConical _•_ e = isProp× (isPropLeftConical _•_ e) (isPropRightConical _•_ e)

  isPropDistrˡ : (_*_ _+_ : Op₂ A) → isProp (_*_ DistributesOverˡ _+_)
  isPropDistrˡ _ _ = isPropΠ3 λ _ _ _ → isSetA _ _

  isPropDistrʳ : (_*_ _+_ : Op₂ A) → isProp (_*_ DistributesOverʳ _+_)
  isPropDistrʳ _ _ = isPropΠ3 λ _ _ _ → isSetA _ _

  isPropDistr : (_*_ _+_ : Op₂ A) → isProp (_*_ DistributesOver _+_)
  isPropDistr _*_ _+_ = isProp× (isPropDistrˡ _*_ _+_) (isPropDistrʳ _*_ _+_)

  isPropIdempotentOn : (_•_ : Op₂ A) (x : A) → isProp (_•_ IdempotentOn x)
  isPropIdempotentOn _ _ = isSetA _ _

  isPropIdempotent : (_•_ : Op₂ A) → isProp (Idempotent _•_)
  isPropIdempotent _•_ = isPropΠ λ x → isPropIdempotentOn _•_ x

  isPropIdempotentFun : (f : Op₁ A) → isProp (IdempotentFun f)
  isPropIdempotentFun _ = isPropΠ λ _ → isSetA _ _

  isPropSelective : (_•_ : Op₂ A) → isProp (Selective _•_)
  isPropSelective _ = isPropΠ2 λ _ _ → squash

  isPropAbsorbs : (_⋀_ _⋁_ : Op₂ A) → isProp (_⋀_ Absorbs _⋁_)
  isPropAbsorbs _ _ = isPropΠ2 λ _ _ → isSetA _ _

  isPropAbsorptive : (_⋀_ _⋁_ : Op₂ A) → isProp (Absorptive _⋀_ _⋁_)
  isPropAbsorptive _⋀_ _⋁_ = isProp× (isPropAbsorbs _⋀_ _⋁_) (isPropAbsorbs _⋁_ _⋀_)

  isPropInvolutive : (f : Op₁ A) → isProp (Involutive f)
  isPropInvolutive _ = isPropΠ λ _ → isSetA _ _

  isPropLeftCancel : (_•_ : Op₂ A) → isProp (LeftCancellative _•_)
  isPropLeftCancel _ = isPropΠ λ _ → isPropImpΠ2 λ _ _ → isPropΠ λ _ → isSetA _ _

  isPropRightCancel : (_•_ : Op₂ A) → isProp (RightCancellative _•_)
  isPropRightCancel _ = isPropImpΠ2 λ _ _ → isPropΠ2 λ _ _ → isSetA _ _

  isPropCancellative : (_•_ : Op₂ A) → isProp (Cancellative _•_)
  isPropCancellative _•_ = isProp× (isPropLeftCancel _•_) (isPropRightCancel _•_)

  isPropInterchangeable : (_•_ _◦_ : Op₂ A) → isProp (Interchangeable _•_ _◦_)
  isPropInterchangeable _ _ = isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → isSetA _ _


  sel⇒idem : {_•_ : Op₂ A} → Selective _•_ → Idempotent _•_
  sel⇒idem {_•_ = _•_} sel x = rec (isPropIdempotentOn _•_ x)
    (λ { (inl p) → p
       ; (inr p) → p
      })
    (sel x x)

module _ {ℓ′} {B : Type ℓ′} (isSetB : isSet B) where

  isPropHomomorphic₀ : (f : A → B) (x : A) (y : B) → isProp (Homomorphic₀ f x y)
  isPropHomomorphic₀ _ _ _ = isSetB _ _

  isPropHomomorphic₁ : (f : A → B) (g : Op₁ A) (h : Op₁ B) → isProp (Homomorphic₁ f g h)
  isPropHomomorphic₁ _ _ _ = isPropΠ λ _ → isSetB _ _

  isPropHomomorphic₂ : (f : A → B) (• : Op₂ A) (◦ : Op₂ B) → isProp (Homomorphic₂ f • ◦)
  isPropHomomorphic₂ _ _ _ = isPropΠ2 λ _ _ → isSetB _ _

id-unique′ : ∀ {_•_ : Op₂ A} {e i} → LeftIdentity e _•_ → RightIdentity i _•_ → e ≡ i
id-unique′ {_} {_} {_•_} {e} {i} idˡ idʳ =
  e     ≡˘⟨ idʳ e ⟩
  e • i ≡⟨ idˡ i ⟩
  i     ∎

id-unique : ∀ {_•_ : Op₂ A} {e i} → Identity e _•_ → Identity i _•_ → e ≡ i
id-unique (idˡ , _) (_ , idʳ) = id-unique′ idˡ idʳ

id-collapseʳ : ∀ {_•_ : Op₂ A} {e i} → LeftIdentity e _•_ → RightIdentity i _•_ → Identity e _•_
id-collapseʳ {_} {_} {_•_} idˡ idʳ = idˡ , subst (λ e → RightIdentity e _•_) (sym (id-unique′ idˡ idʳ)) idʳ

id-collapseˡ : ∀ {_•_ : Op₂ A} {e i} → LeftIdentity e _•_ → RightIdentity i _•_ → Identity i _•_
id-collapseˡ {_} {_} {_•_} idˡ idʳ = subst (λ e → LeftIdentity e _•_) (id-unique′ idˡ idʳ) idˡ , idʳ

------------------------------------------------------------------------
-- Magma-like Algebra

module _ {_•_ : Op₂ A} (comm : Commutative _•_) where

  comm+cancelˡ⇒cancelʳ : LeftCancellative _•_ → RightCancellative _•_
  comm+cancelˡ⇒cancelʳ cancelˡ {x = x} {y} z eq = cancelˡ z (
    z • x ≡⟨ comm z x ⟩
    x • z ≡⟨ eq ⟩
    y • z ≡⟨ comm y z ⟩
    z • y ∎)

  comm+cancelʳ⇒cancelˡ : RightCancellative _•_ → LeftCancellative _•_
  comm+cancelʳ⇒cancelˡ cancelʳ x {y} {z} eq = cancelʳ x (
    y • x ≡⟨ comm y x ⟩
    x • y ≡⟨ eq ⟩
    x • z ≡⟨ comm x z ⟩
    z • x ∎)

------------------------------------------------------------------------
-- Monoid-like Algebra

module _ {_•_ : Op₂ A} (comm : Commutative _•_) {e : A} where

  comm+idˡ⇒idʳ : LeftIdentity e _•_ → RightIdentity e _•_
  comm+idˡ⇒idʳ idˡ x =
    x • e ≡⟨ comm x e ⟩
    e • x ≡⟨ idˡ x ⟩
    x     ∎

  comm+idʳ⇒idˡ : RightIdentity e _•_ → LeftIdentity e _•_
  comm+idʳ⇒idˡ idʳ x =
    e • x ≡⟨ comm e x ⟩
    x • e ≡⟨ idʳ x ⟩
    x     ∎

  comm+zeˡ⇒zeʳ : LeftZero e _•_ → RightZero e _•_
  comm+zeˡ⇒zeʳ zeˡ x =
    x • e ≡⟨ comm x e ⟩
    e • x ≡⟨ zeˡ x ⟩
    e     ∎

  comm+zeʳ⇒zeˡ : RightZero e _•_ → LeftZero e _•_
  comm+zeʳ⇒zeˡ zeʳ x =
    e • x ≡⟨ comm e x ⟩
    x • e ≡⟨ zeʳ x ⟩
    e     ∎

------------------------------------------------------------------------
-- Group-like Algebra

module _ {_•_ : Op₂ A} {_⁻¹ : Op₁ A} {e} (comm : Commutative _•_) where

  comm+invˡ⇒invʳ : LeftInverse e _⁻¹ _•_ → RightInverse e _⁻¹ _•_
  comm+invˡ⇒invʳ invˡ x =
    x • (x ⁻¹) ≡⟨ comm x (x ⁻¹) ⟩
    (x ⁻¹) • x ≡⟨ invˡ x ⟩
    e          ∎

  comm+invʳ⇒invˡ : RightInverse e _⁻¹ _•_ → LeftInverse e _⁻¹ _•_
  comm+invʳ⇒invˡ invʳ x =
    (x ⁻¹) • x ≡⟨ comm (x ⁻¹) x ⟩
    x • (x ⁻¹) ≡⟨ invʳ x ⟩
    e          ∎

module _ {_•_ : Op₂ A} {_⁻¹ : Op₁ A} {e} where

  assoc+id+invʳ⇒invʳ-unique : Associative _•_ →
                              Identity e _•_ → RightInverse e _⁻¹ _•_ →
                              ∀ x y → (x • y) ≡ e → x ≡ (y ⁻¹)
  assoc+id+invʳ⇒invʳ-unique assoc (idˡ , idʳ) invʳ x y eq =
    x                ≡⟨ sym (idʳ x) ⟩
    x • e            ≡˘⟨ cong (x •_) (invʳ y) ⟩
    x • (y • (y ⁻¹)) ≡˘⟨ assoc x y (y ⁻¹) ⟩
    (x • y) • (y ⁻¹) ≡⟨ cong (_• (y ⁻¹)) eq ⟩
    e • (y ⁻¹)       ≡⟨ idˡ (y ⁻¹) ⟩
    y ⁻¹             ∎

  assoc+id+invˡ⇒invˡ-unique : Associative _•_ →
                              Identity e _•_ → LeftInverse e _⁻¹ _•_ →
                              ∀ x y → (x • y) ≡ e → y ≡ (x ⁻¹)
  assoc+id+invˡ⇒invˡ-unique assoc (idˡ , idʳ) invˡ x y eq =
    y                ≡˘⟨ idˡ y ⟩
    e • y            ≡˘⟨ cong (_• y) (invˡ x) ⟩
    ((x ⁻¹) • x) • y ≡⟨ assoc (x ⁻¹) x y ⟩
    (x ⁻¹) • (x • y) ≡⟨ cong ((x ⁻¹) •_) eq ⟩
    (x ⁻¹) • e       ≡⟨ idʳ (x ⁻¹) ⟩
    x ⁻¹             ∎

  assoc+idˡ+invˡ⇒cancelˡ : Associative _•_ →
                          LeftIdentity e _•_ → LeftInverse e _⁻¹ _•_ →
                          LeftCancellative _•_
  assoc+idˡ+invˡ⇒cancelˡ assoc idˡ invˡ x {y} {z} eq =
    y                ≡˘⟨ idˡ y ⟩
    e • y            ≡˘⟨ cong (_• y) (invˡ x) ⟩
    ((x ⁻¹) • x) • y ≡⟨ assoc (x ⁻¹) x y ⟩
    (x ⁻¹) • (x • y) ≡⟨ cong ((x ⁻¹) •_) eq ⟩
    (x ⁻¹) • (x • z) ≡˘⟨ assoc (x ⁻¹) x z ⟩
    ((x ⁻¹) • x) • z ≡⟨ cong (_• z) (invˡ x) ⟩
    e • z            ≡⟨ idˡ z ⟩
    z                ∎

  assoc+idʳ+invʳ⇒cancelʳ : Associative _•_ →
                          RightIdentity e _•_ → RightInverse e _⁻¹ _•_ →
                          RightCancellative _•_
  assoc+idʳ+invʳ⇒cancelʳ assoc idʳ invʳ {x} {y} z eq =
    x                ≡˘⟨ idʳ x ⟩
    x • e            ≡˘⟨ cong (x •_) (invʳ z) ⟩
    x • (z • (z ⁻¹)) ≡˘⟨ assoc x z (z ⁻¹) ⟩
    (x • z) • (z ⁻¹) ≡⟨ cong (_• (z ⁻¹)) eq ⟩
    (y • z) • (z ⁻¹) ≡⟨ assoc y z (z ⁻¹) ⟩
    y • (z • (z ⁻¹)) ≡⟨ cong (y •_) (invʳ z) ⟩
    y • e            ≡⟨ idʳ y ⟩
    y                ∎


----------------------------------------------------------------------
-- Bisemigroup-like Algebra

module _ {_*_ _+_ : Op₂ A} (*-comm : Commutative _*_) where

  comm+distrˡ⇒distrʳ :  _*_ DistributesOverˡ _+_ → _*_ DistributesOverʳ _+_
  comm+distrˡ⇒distrʳ distrˡ x y z =
    (y + z) * x       ≡⟨ *-comm (y + z) x ⟩
    x * (y + z)       ≡⟨ distrˡ x y z ⟩
    (x * y) + (x * z) ≡⟨ cong₂ _+_ (*-comm x y) (*-comm x z) ⟩
    (y * x) + (z * x) ∎

  comm+distrʳ⇒distrˡ : _*_ DistributesOverʳ _+_ → _*_ DistributesOverˡ _+_
  comm+distrʳ⇒distrˡ distrʳ x y z =
    x * (y + z)       ≡⟨ *-comm x (y + z) ⟩
    (y + z) * x       ≡⟨ distrʳ x y z ⟩
    (y * x) + (z * x) ≡⟨ cong₂ _+_ (*-comm y x) (*-comm z x) ⟩
    (x * y) + (x * z) ∎

----------------------------------------------------------------------
-- Ring-like Algebra

module _ {_+_ _*_ : Op₂ A} { -_ : Op₁ A} {0# : A} where

  assoc+distribʳ+idʳ+invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                                LeftZero 0# _*_
  assoc+distribʳ+idʳ+invʳ⇒zeˡ +-assoc distribʳ idʳ invʳ x =
    0# * x                              ≡⟨ sym (idʳ _) ⟩
    (0# * x) + 0#                       ≡˘⟨ cong ((0# * x) +_) (invʳ _) ⟩
    (0# * x) + ((0# * x) + (-(0# * x))) ≡˘⟨ +-assoc _ _ _ ⟩
    ((0# * x) + (0# * x)) + (-(0# * x)) ≡˘⟨ cong (_+ (-(0# * x))) (distribʳ _ _ _) ⟩
    ((0# + 0#) * x) + (-(0# * x))       ≡⟨ cong (λ v → (v * x) + (-(0# * x))) (idʳ 0#) ⟩
    (0# * x) + (-(0# * x))              ≡⟨ invʳ _ ⟩
    0#                                  ∎

  assoc+distribˡ+idʳ+invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                                RightZero 0# _*_
  assoc+distribˡ+idʳ+invʳ⇒zeʳ +-assoc distribˡ idʳ invʳ x =
     x * 0#                              ≡⟨ sym (idʳ _) ⟩
     (x * 0#) + 0#                       ≡˘⟨ cong ((x * 0#) +_) (invʳ _) ⟩
     (x * 0#) + ((x * 0#) + (-(x * 0#))) ≡˘⟨ +-assoc _ _ _ ⟩
     ((x * 0#) + (x * 0#)) + (-(x * 0#)) ≡˘⟨ cong (_+ (-(x * 0#))) (distribˡ _ _ _) ⟩
     (x * (0# + 0#)) + (-(x * 0#))       ≡⟨ cong (λ v → (x * v) + (-(x * 0#))) (idʳ 0#) ⟩
     (x * 0#) + (-(x * 0#))              ≡⟨ invʳ _ ⟩
     0#                                  ∎

----------------------------------------------------------------------
-- Other

module _ {c ℓ} {A : Type c} (R : Rel A ℓ) (reflexive : Reflexive R) (• : Op₂ A) where

  cong₂⇒lcong : Congruent₂ R • → LeftCongruent R •
  cong₂⇒lcong cong₂ {x} {y} {z} yRz = cong₂ reflexive yRz

  cong₂⇒rcong : Congruent₂ R • → RightCongruent R •
  cong₂⇒rcong cong₂ {x} {y} {z} yRz = cong₂ yRz reflexive

module _ {c ℓ} {A : Type c} (R : Rel A ℓ) (transitive : Transitive R) (• : Op₂ A) where

  lcong+rcong⇒cong₂ : LeftCongruent R • → RightCongruent R • → Congruent₂ R •
  lcong+rcong⇒cong₂ lcong rcong xRy uRv = transitive (lcong uRv) (rcong xRy)
