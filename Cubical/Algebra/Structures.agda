{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything

module Cubical.Algebra.Structures {a} (A : Type a) where

-- The file is divided into sections depending on the arities of the
-- components of the algebraic structure.

open import Cubical.Foundations.Prelude using (isSet; cong; _∙_)
open import Cubical.Foundations.HLevels using (hSet)

open import Cubical.Algebra.Base
open import Cubical.Algebra.Definitions
open import Cubical.Algebra.Properties
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Data.Nat.Base renaming (zero to ℕ-zero; suc to ℕ-suc)
open import Cubical.Data.Int.Base
open import Cubical.Data.NatPlusOne.Base

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Reasoning.Equality

_NotEqualTo_ : A → Type a
_NotEqualTo_ z = Σ[ x ∈ A ] ¬ (x ≡ z)

------------------------------------------------------------------------
-- Algebra with 1 binary operation
------------------------------------------------------------------------

record IsMagma (_•_ : Op₂ A) : Type a where
  constructor ismagma
  field
    is-set : isSet A

  set : hSet a
  set = A , is-set


record IsSemigroup (_•_ : Op₂ A) : Type a where
  constructor issemigroup
  field
    isMagma : IsMagma _•_
    assoc   : Associative _•_

  open IsMagma isMagma public

  infixl 10 _^_
  _^_ : A → ℕ₊₁ → A
  x ^ one    = x
  x ^ (2+ n) = x • (x ^ 1+ n)


record IsBand (_•_ : Op₂ A) : Type a where
  constructor isband
  field
    isSemigroup : IsSemigroup _•_
    idem        : Idempotent _•_

  open IsSemigroup isSemigroup public


record IsCommutativeSemigroup (_•_ : Op₂ A) : Type a where
  constructor iscommsemigroup
  field
    isSemigroup : IsSemigroup _•_
    comm        : Commutative _•_

  open IsSemigroup isSemigroup public


record IsSemilattice (_•_ : Op₂ A) : Type a where
  constructor issemilattice
  field
    isBand : IsBand _•_
    comm   : Commutative _•_

  open IsBand isBand public


record IsSelectiveMagma (_•_ : Op₂ A) : Type a where
  constructor isselmagma
  field
    isMagma : IsMagma _•_
    sel     : Selective _•_

  open IsMagma isMagma public


------------------------------------------------------------------------
-- Algebra with 1 binary operation & 1 element
------------------------------------------------------------------------

record IsMonoid (_•_ : Op₂ A) (ε : A) : Type a where
  constructor ismonoid
  field
    isSemigroup : IsSemigroup _•_
    identity    : Identity ε _•_

  open IsSemigroup isSemigroup public hiding (_^_)

  identityˡ : LeftIdentity ε _•_
  identityˡ = fst identity

  identityʳ : RightIdentity ε _•_
  identityʳ = snd identity

  ε-uniqueʳ : ∀ {e} → RightIdentity e _•_ → ε ≡ e
  ε-uniqueʳ idʳ = id-unique′ identityˡ idʳ

  ε-uniqueˡ : ∀ {e} → LeftIdentity e _•_ → e ≡ ε
  ε-uniqueˡ idˡ = id-unique′ idˡ identityʳ

  infixl 10 _^_
  _^_ : A → ℕ → A
  _ ^ ℕ-zero    = ε
  x ^ (ℕ-suc n) = x • (x ^ n)


record IsCommutativeMonoid (_•_ : Op₂ A) (ε : A) : Type a where
  constructor iscommmonoid
  field
    isMonoid : IsMonoid _•_ ε
    comm     : Commutative _•_

  open IsMonoid isMonoid public

  isCommutativeSemigroup : IsCommutativeSemigroup _•_
  isCommutativeSemigroup = record
    { isSemigroup = isSemigroup
    ; comm        = comm
    }


record IsIdempotentCommutativeMonoid (_•_ : Op₂ A) (ε : A) : Type a where
  constructor isidemcommmonoid
  field
    isCommutativeMonoid : IsCommutativeMonoid _•_ ε
    idem                : Idempotent _•_

  open IsCommutativeMonoid isCommutativeMonoid public


-- Idempotent commutative monoids are also known as bounded lattices.
-- Note that the BoundedLattice necessarily uses the notation inherited
-- from monoids rather than lattices.

IsBoundedLattice = IsIdempotentCommutativeMonoid
pattern isboundedlattice = isidemcommmonoid

module IsBoundedLattice {_•_ : Op₂ A}
                        {ε : A}
                        (isIdemCommMonoid : IsIdempotentCommutativeMonoid _•_ ε) =
       IsIdempotentCommutativeMonoid isIdemCommMonoid


------------------------------------------------------------------------
-- Algebra with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------

record IsGroup (_•_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Type a where
  constructor isgroup
  field
    isMonoid  : IsMonoid _•_ ε
    inverse   : Inverse ε _⁻¹ _•_

  open IsMonoid isMonoid public hiding (_^_)

  infixl 10 _^_
  _^_ : A → ℤ → A
  x ^ pos ℕ-zero       = ε
  x ^ pos (ℕ-suc n)    = x • (x ^ pos n)
  x ^ negsuc ℕ-zero    = x ⁻¹
  x ^ negsuc (ℕ-suc n) = (x ⁻¹) • (x ^ negsuc n)

  -- Right division
  infixl 6 _/_
  _/_ : Op₂ A
  x / y = x • (y ⁻¹)

  -- Left division
  infixr 6 _/ˡ_
  _/ˡ_ : Op₂ A
  x /ˡ y = (x ⁻¹) • y

  inverseˡ : LeftInverse ε _⁻¹ _•_
  inverseˡ = fst inverse

  inverseʳ : RightInverse ε _⁻¹ _•_
  inverseʳ = snd inverse

  inv-uniqueʳ : ∀ x y → (x • y) ≡ ε → x ≡ (y ⁻¹)
  inv-uniqueʳ = assoc+id+invʳ⇒invʳ-unique assoc identity inverseʳ

  inv-uniqueˡ : ∀ x y → (x • y) ≡ ε → y ≡ (x ⁻¹)
  inv-uniqueˡ = assoc+id+invˡ⇒invˡ-unique assoc identity inverseˡ

  cancelˡ : LeftCancellative _•_
  cancelˡ = assoc+idˡ+invˡ⇒cancelˡ assoc identityˡ inverseˡ

  cancelʳ : RightCancellative _•_
  cancelʳ = assoc+idʳ+invʳ⇒cancelʳ assoc identityʳ inverseʳ


record IsAbelianGroup (_+_ : Op₂ A) (ε : A) (-_ : Op₁ A) : Type a where
  constructor isabgroup
  field
    isGroup : IsGroup _+_ ε -_
    comm    : Commutative _+_

  open IsGroup isGroup public hiding (_/ˡ_) renaming (_/_ to _-_; _^_ to _*_)

  isCommutativeMonoid : IsCommutativeMonoid _+_ ε
  isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm     = comm
    }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeSemigroup)


------------------------------------------------------------------------
-- Algebra with 2 binary operations
------------------------------------------------------------------------

-- Note that `IsLattice` is not defined in terms of `IsSemilattice`
-- because the idempotence laws of ⋀ and ⋁ can be derived from the
-- absorption laws, which makes the corresponding "idem" fields
-- redundant.  The derived idempotence laws are stated and proved in
-- `Algebra.Properties.Lattice` along with the fact that every lattice
-- consists of two semilattices.

record IsLattice (_⋀_ _⋁_ : Op₂ A) : Type a where
  constructor islattice
  field
    ⋀-comm        : Commutative _⋀_
    ⋀-assoc       : Associative _⋀_
    ⋁-comm        : Commutative _⋁_
    ⋁-assoc       : Associative _⋁_
    absorptive    : Absorptive _⋀_ _⋁_

  ⋀-absorbs-⋁ : _⋀_ Absorbs _⋁_
  ⋀-absorbs-⋁ = fst absorptive

  ⋁-absorbs-⋀ : _⋁_ Absorbs _⋀_
  ⋁-absorbs-⋀ = snd absorptive


record IsDistributiveLattice (_⋀_ _⋁_ : Op₂ A) : Type a where
  constructor isdistrlattice
  field
    isLattice    : IsLattice _⋀_ _⋁_
    ⋀-distribʳ-⋁ : _⋀_ DistributesOverʳ _⋁_

  open IsLattice isLattice public

------------------------------------------------------------------------
-- Algebra with 2 binary operations & 1 element
------------------------------------------------------------------------

record IsNearSemiring (_+_ _*_ : Op₂ A) (0# : A) : Type a where
  constructor isnearsemiring
  field
    +-isMonoid    : IsMonoid _+_ 0#
    *-isSemigroup : IsSemigroup _*_
    distribˡ      : _*_ DistributesOverˡ _+_
    zeroˡ         : LeftZero 0# _*_

  open IsMonoid +-isMonoid public
    renaming
    ( assoc       to +-assoc
    ; identity    to +-identity
    ; identityˡ   to +-identityˡ
    ; identityʳ   to +-identityʳ
    ; ε-uniqueˡ   to 0#-uniqueˡ
    ; ε-uniqueʳ   to 0#-uniqueʳ
    ; isMagma     to +-isMagma
    ; isSemigroup to +-isSemigroup
    ; _^_         to _**_
    )

  open IsSemigroup *-isSemigroup public
    using (_^_)
    renaming
    ( assoc    to *-assoc
    ; isMagma  to *-isMagma
    )


record IsSemiringWithoutOne (_+_ _*_ : Op₂ A) (0# : A) : Type a where
  constructor issemiringwo1
  field
    +-isCommutativeMonoid : IsCommutativeMonoid _+_ 0#
    *-isSemigroup         : IsSemigroup _*_
    distrib               : _*_ DistributesOver _+_
    zero                  : Zero 0# _*_

  open IsCommutativeMonoid +-isCommutativeMonoid public
    using ()
    renaming
    ( comm                   to +-comm
    ; isMonoid               to +-isMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    )

  zeroˡ : LeftZero 0# _*_
  zeroˡ = fst zero

  zeroʳ : RightZero 0# _*_
  zeroʳ = snd zero

  distribˡ : _*_ DistributesOverˡ _+_
  distribˡ = fst distrib

  distribʳ : _*_ DistributesOverʳ _+_
  distribʳ = snd distrib

  isNearSemiring : IsNearSemiring _+_ _*_ 0#
  isNearSemiring = record
    { +-isMonoid    = +-isMonoid
    ; *-isSemigroup = *-isSemigroup
    ; distribˡ      = distribˡ
    ; zeroˡ         = zeroˡ
    }

  open IsNearSemiring isNearSemiring public
    hiding (+-isMonoid; zeroˡ; *-isSemigroup; distribˡ)


record IsCommutativeSemiringWithoutOne (_+_ _*_ : Op₂ A) (0# : A) : Type a where
  constructor iscommsemiringwo1
  field
    isSemiringWithoutOne : IsSemiringWithoutOne _+_ _*_ 0#
    *-comm               : Commutative _*_

  open IsSemiringWithoutOne isSemiringWithoutOne public


------------------------------------------------------------------------
-- Algebra with 2 binary operations & 2 elements
------------------------------------------------------------------------

record IsSemiringWithoutAnnihilatingZero (_+_ _*_ : Op₂ A)
                                         (0# 1# : A) : Type a where
  constructor issemiringwoa0
  field
    -- Note that these Algebra do have an additive unit, but this
    -- unit does not necessarily annihilate multiplication.
    +-isCommutativeMonoid : IsCommutativeMonoid _+_ 0#
    *-isMonoid            : IsMonoid _*_ 1#
    distrib               : _*_ DistributesOver _+_

  distribˡ : _*_ DistributesOverˡ _+_
  distribˡ = fst distrib

  distribʳ : _*_ DistributesOverʳ _+_
  distribʳ = snd distrib

  open IsCommutativeMonoid +-isCommutativeMonoid public
    renaming
    ( assoc                  to +-assoc
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; ε-uniqueˡ              to 0#-uniqueˡ
    ; ε-uniqueʳ              to 0#-uniqueʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; _^_                    to _**_
    )

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( assoc       to *-assoc
    ; identity    to *-identity
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; ε-uniqueˡ   to 1#-uniqueˡ
    ; ε-uniqueʳ   to 1#-uniqueʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    )


record IsSemiring (_+_ _*_ : Op₂ A) (0# 1# : A) : Type a where
  constructor issemiring
  field
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero _+_ _*_ 0# 1#
    zero : Zero 0# _*_

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  isSemiringWithoutOne : IsSemiringWithoutOne _+_ _*_ 0#
  isSemiringWithoutOne = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isSemigroup         = *-isSemigroup
    ; distrib               = distrib
    ; zero                  = zero
    }

  open IsSemiringWithoutOne isSemiringWithoutOne public
    using
    ( isNearSemiring
    ; zeroˡ
    ; zeroʳ
    )


record IsCommutativeSemiring (_+_ _*_ : Op₂ A) (0# 1# : A) : Type a where
  constructor iscommsemiring
  field
    isSemiring : IsSemiring _+_ _*_ 0# 1#
    *-comm     : Commutative _*_

  open IsSemiring isSemiring public

  isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne _+_ _*_ 0#
  isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = isSemiringWithoutOne
    ; *-comm = *-comm
    }

  *-isCommutativeSemigroup : IsCommutativeSemigroup _*_
  *-isCommutativeSemigroup = record
    { isSemigroup = *-isSemigroup
    ; comm        = *-comm
    }

  *-isCommutativeMonoid : IsCommutativeMonoid _*_ 1#
  *-isCommutativeMonoid = record
    { isMonoid = *-isMonoid
    ; comm     = *-comm
    }


------------------------------------------------------------------------
-- Algebra with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

record IsRing (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Type a where
  constructor isring
  field
    +-isAbelianGroup : IsAbelianGroup _+_ 0# -_
    *-isMonoid       : IsMonoid _*_ 1#
    distrib          : _*_ DistributesOver _+_

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                  to +-assoc
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; ε-uniqueˡ              to 0#-uniqueˡ
    ; ε-uniqueʳ              to 0#-uniqueʳ
    ; inverse                to +-inverse
    ; inverseˡ               to +-inverseˡ
    ; inverseʳ               to +-inverseʳ
    ; inv-uniqueˡ            to neg-uniqueˡ
    ; inv-uniqueʳ            to neg-uniqueʳ
    ; cancelˡ                to +-cancelˡ
    ; cancelʳ                to +-cancelʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isGroup                to +-isGroup
    ; _*_                    to _**_
    )

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( assoc       to *-assoc
    ; identity    to *-identity
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; ε-uniqueˡ   to 1#-uniqueˡ
    ; ε-uniqueʳ   to 1#-uniqueʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    )

  distribˡ : _*_ DistributesOverˡ _+_
  distribˡ = fst distrib

  distribʳ : _*_ DistributesOverʳ _+_
  distribʳ = snd distrib

  zeroˡ : LeftZero 0# _*_
  zeroˡ = assoc+distribʳ+idʳ+invʳ⇒zeˡ {_+_ = _+_} {_*_ = _*_} { -_} +-assoc distribʳ +-identityʳ +-inverseʳ

  zeroʳ : RightZero 0# _*_
  zeroʳ = assoc+distribˡ+idʳ+invʳ⇒zeʳ {_+_ = _+_} {_*_ = _*_} { -_} +-assoc distribˡ +-identityʳ +-inverseʳ

  zero : Zero 0# _*_
  zero = zeroˡ , zeroʳ

  isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero _+_ _*_ 0# 1#
  isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isMonoid            = *-isMonoid
    ; distrib               = distrib
    }

  isSemiring : IsSemiring _+_ _*_ 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    ; zero = zero
    }

  open IsSemiring isSemiring public
    using (isNearSemiring; isSemiringWithoutOne)


record IsCommutativeRing (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Type a where
  constructor iscommring
  field
    isRing : IsRing _+_ _*_ -_ 0# 1#
    *-comm : Commutative _*_

  open IsRing isRing public

  *-isCommutativeMonoid : IsCommutativeMonoid _*_ 1#
  *-isCommutativeMonoid =  record
    { isMonoid = *-isMonoid
    ; comm     = *-comm
    }

  isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0# 1#
  isCommutativeSemiring = record
    { isSemiring = isSemiring
    ; *-comm = *-comm
    }

  open IsCommutativeSemiring isCommutativeSemiring public
    using ( isCommutativeSemiringWithoutOne )

record IsIntegralDomain {ℓ} (Cancellable : A → Type ℓ) (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Type (ℓ-max a ℓ) where
  constructor isintegraldomain

  Cancellables : Type (ℓ-max a ℓ)
  Cancellables = Σ A Cancellable

  field
    isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#
    *-cancelˡ         : ∀ (x : Cancellables) {y z} → (x .fst) * y ≡ (x .fst) * z → y ≡ z

  open IsCommutativeRing isCommutativeRing public

  *-cancelʳ : ∀ {x y} (z : Cancellables) → x * (z .fst) ≡ y * (z .fst) → x ≡ y
  *-cancelʳ {x} {y} zᵖ@(z , _) eq = *-cancelˡ zᵖ (
    z * x ≡⟨ *-comm z x ⟩
    x * z ≡⟨ eq ⟩
    y * z ≡⟨ *-comm y z ⟩
    z * y ∎)

record IsBooleanAlgebra (_⋀_ _⋁_ : Op₂ A) (¬_ : Op₁ A) (⊤ ⊥ : A) : Type a where
  constructor isbooleanalgebra
  field
    isDistributiveLattice : IsDistributiveLattice _⋀_ _⋁_
    ⋀-identityʳ           : RightIdentity ⊤ _⋀_
    ⋁-identityʳ           : RightIdentity ⊥ _⋁_
    ⋀-complementʳ         : RightInverse ⊥ ¬_ _⋀_
    ⋁-complementʳ         : RightInverse ⊤ ¬_ _⋁_

  open IsDistributiveLattice isDistributiveLattice public

  ⋀-identityˡ : LeftIdentity ⊤ _⋀_
  ⋀-identityˡ x = ⋀-comm _ _ ∙ ⋀-identityʳ x

  ⋀-identity : Identity ⊤ _⋀_
  ⋀-identity = ⋀-identityˡ , ⋀-identityʳ

  ⋁-identityˡ : LeftIdentity ⊥ _⋁_
  ⋁-identityˡ x = ⋁-comm _ _ ∙ ⋁-identityʳ x

  ⋁-identity : Identity ⊥ _⋁_
  ⋁-identity = ⋁-identityˡ , ⋁-identityʳ

  ⋀-complementˡ : LeftInverse ⊥ ¬_ _⋀_
  ⋀-complementˡ = comm+invʳ⇒invˡ ⋀-comm ⋀-complementʳ

  ⋀-complement : Inverse ⊥ ¬_ _⋀_
  ⋀-complement = ⋀-complementˡ , ⋀-complementʳ

  ⋁-complementˡ : LeftInverse ⊤ ¬_ _⋁_
  ⋁-complementˡ = comm+invʳ⇒invˡ ⋁-comm ⋁-complementʳ

  ⋁-complement : Inverse ⊤ ¬_ _⋁_
  ⋁-complement = ⋁-complementˡ , ⋁-complementʳ


------------------------------------------------------------------------
-- Algebra with 2 binary operations, 2 unary operations & 2 elements
------------------------------------------------------------------------

-- The standard definition of division rings excludes the zero ring, but such a restriction is rarely important
record IsDivisionRing {ℓ} (Invertible : A → Type ℓ) (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (_⁻¹ : Σ A Invertible → A) (0# 1# : A) : Type (ℓ-max a ℓ) where
  constructor isdivring

  Invertibles : Type (ℓ-max a ℓ)
  Invertibles = Σ A Invertible

  field
    isRing   : IsRing _+_ _*_ -_ 0# 1#
    *-inverseˡ : (x : Invertibles) → (x ⁻¹) * (x .fst) ≡ 1#
    *-inverseʳ : (x : Invertibles) → (x .fst) * (x ⁻¹) ≡ 1#

  open IsRing isRing public

  infixl 6 _/_
  _/_ : A → Invertibles → A
  x / y = x * (y ⁻¹)

  infixr 6 _/ˡ_
  _/ˡ_ : Invertibles → A → A
  x /ˡ y = (x ⁻¹) * y

  *-cancelˡ : ∀ (x : Invertibles) {y z} → (x .fst) * y ≡ (x .fst) * z → y ≡ z
  *-cancelˡ xᵖ@(x , _) {y} {z} eq =
    y                 ≡˘⟨ *-identityˡ y ⟩
    1# * y            ≡˘⟨ cong (_* y) (*-inverseˡ xᵖ) ⟩
    ((xᵖ ⁻¹) * x) * y ≡⟨ *-assoc (xᵖ ⁻¹) x y ⟩
    (xᵖ ⁻¹) * (x * y) ≡⟨ cong ((xᵖ ⁻¹) *_) eq ⟩
    (xᵖ ⁻¹) * (x * z) ≡˘⟨ *-assoc (xᵖ ⁻¹) x z ⟩
    ((xᵖ ⁻¹) * x) * z ≡⟨ cong (_* z) (*-inverseˡ xᵖ) ⟩
    1# * z            ≡⟨ *-identityˡ z ⟩
    z                 ∎

  *-cancelʳ : ∀ {x y} (z : Invertibles) → x * (z .fst) ≡ y * (z .fst) → x ≡ y
  *-cancelʳ {x} {y} zᵖ@(z , _) eq =
    x                 ≡˘⟨ *-identityʳ x ⟩
    x * 1#            ≡˘⟨ cong (x *_) (*-inverseʳ zᵖ) ⟩
    x * (z * (zᵖ ⁻¹)) ≡˘⟨ *-assoc x z (zᵖ ⁻¹) ⟩
    (x * z) * (zᵖ ⁻¹) ≡⟨ cong (_* (zᵖ ⁻¹)) eq ⟩
    (y * z) * (zᵖ ⁻¹) ≡⟨ *-assoc y z (zᵖ ⁻¹) ⟩
    y * (z * (zᵖ ⁻¹)) ≡⟨ cong (y *_) (*-inverseʳ zᵖ) ⟩
    y * 1#            ≡⟨ *-identityʳ y ⟩
    y                 ∎


record IsField {ℓ} (Invertible : A → Type ℓ) (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (_⁻¹ : Σ A Invertible → A) (0# 1# : A) : Type (ℓ-max a ℓ) where
  constructor isfield
  field
    isDivisionRing : IsDivisionRing Invertible _+_ _*_ -_ _⁻¹ 0# 1#
    *-comm         : Commutative _*_

  open IsDivisionRing isDivisionRing public hiding (_/ˡ_)

  isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#
  isCommutativeRing = record
    { isRing = isRing
    ; *-comm = *-comm
    }

  isIntegralDomain : IsIntegralDomain Invertible _+_ _*_ -_ 0# 1#
  isIntegralDomain = record
    { isCommutativeRing = isCommutativeRing
    ; *-cancelˡ         = *-cancelˡ
    }

  open IsIntegralDomain isIntegralDomain public
    using (*-isCommutativeMonoid; isCommutativeSemiring; isCommutativeSemiringWithoutOne)
