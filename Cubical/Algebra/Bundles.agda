{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Bundles where

open import Cubical.Core.Everything

open import Cubical.Algebra.Base
open import Cubical.Algebra.Structures
open import Cubical.Relation.Binary
open import Cubical.Foundations.Function

open import Cubical.Structures.Carrier

------------------------------------------------------------------------
-- Bundles with 1 binary operation
------------------------------------------------------------------------

record Magma c : Type (ℓ-suc c) where
  constructor mkmagma
  infix 7 _•_ -- No association - forces parentheses
  field
    Carrier : Type c
    _•_     : Op₂ Carrier
    isMagma : IsMagma Carrier _•_

  open IsMagma isMagma public

instance
  MagmaCarrier : ∀ {c} → HasCarrier (Magma c) c
  MagmaCarrier = record { ⟨_⟩ = Magma.Carrier }


record Semigroup c : Type (ℓ-suc c) where
  constructor mksemigroup
  infixl 7 _•_
  field
    Carrier     : Type c
    _•_         : Op₂ Carrier
    isSemigroup : IsSemigroup Carrier _•_

  open IsSemigroup isSemigroup public

  magma : Magma c
  magma = record { isMagma = isMagma }

instance
  SemigroupCarrier : ∀ {c} → HasCarrier (Semigroup c) c
  SemigroupCarrier = record { ⟨_⟩ = Semigroup.Carrier }


record Band c : Type (ℓ-suc c) where
  constructor mkband
  infixl 7 _•_
  field
    Carrier : Type c
    _•_     : Op₂ Carrier
    isBand  : IsBand Carrier _•_

  open IsBand isBand public

  semigroup : Semigroup c
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (magma)

instance
  BandCarrier : ∀ {c} → HasCarrier (Band c) c
  BandCarrier = record { ⟨_⟩ = Band.Carrier }


record CommutativeSemigroup c : Type (ℓ-suc c) where
  constructor mkcommsemigroup
  infixl 7 _•_
  field
    Carrier                 : Type c
    _•_                     : Op₂ Carrier
    isCommutativeSemigroup  : IsCommutativeSemigroup Carrier _•_

  open IsCommutativeSemigroup isCommutativeSemigroup public

  semigroup : Semigroup c
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (magma)

instance
  CommSemigroupCarrier : ∀ {c} → HasCarrier (CommutativeSemigroup c) c
  CommSemigroupCarrier = record { ⟨_⟩ = CommutativeSemigroup.Carrier }


record Semilattice c : Type (ℓ-suc c) where
  constructor mksemilattice
  infixr 7 _•_
  field
    Carrier       : Type c
    _•_           : Op₂ Carrier
    isSemilattice : IsSemilattice Carrier _•_

  open IsSemilattice isSemilattice public

  band : Band c
  band = record { isBand = isBand }

  open Band band public using (magma; semigroup)

instance
  SemilatticeCarrier : ∀ {c} → HasCarrier (Semilattice c) c
  SemilatticeCarrier = record { ⟨_⟩ = Semilattice.Carrier }


record SelectiveMagma c : Type (ℓ-suc c) where
  constructor mkselmagma
  infixl 7 _•_
  field
    Carrier          : Type c
    _•_              : Op₂ Carrier
    isSelectiveMagma : IsSelectiveMagma Carrier _•_

  open IsSelectiveMagma isSelectiveMagma public

  magma : Magma c
  magma = record { isMagma = isMagma }

instance
  SelectiveMagmaCarrier : ∀ {c} → HasCarrier (SelectiveMagma c) c
  SelectiveMagmaCarrier = record { ⟨_⟩ = SelectiveMagma.Carrier }


------------------------------------------------------------------------
-- Bundles with 1 binary operation & 1 element
------------------------------------------------------------------------

record Monoid c : Type (ℓ-suc c) where
  constructor mkmonoid
  infixl 7 _•_
  field
    Carrier  : Type c
    _•_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid Carrier _•_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup _
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (magma)

instance
  MonoidCarrier : ∀ {c} → HasCarrier (Monoid c) c
  MonoidCarrier = record { ⟨_⟩ = Monoid.Carrier }


record CommutativeMonoid c : Type (ℓ-suc c) where
  constructor mkcommmonoid
  infixl 7 _•_
  field
    Carrier             : Type c
    _•_                 : Op₂ Carrier
    ε                   : Carrier
    isCommutativeMonoid : IsCommutativeMonoid Carrier _•_ ε

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (magma; semigroup)

  commutativeSemigroup : CommutativeSemigroup _
  commutativeSemigroup = record { isCommutativeSemigroup = isCommutativeSemigroup }

instance
  CommMonoidCarrier : ∀ {c} → HasCarrier (CommutativeMonoid c) c
  CommMonoidCarrier = record { ⟨_⟩ = CommutativeMonoid.Carrier }


record IdempotentCommutativeMonoid c : Type (ℓ-suc c) where
  constructor mkidemcommmonoid
  infixl 7 _•_
  field
    Carrier                       : Type c
    _•_                           : Op₂ Carrier
    ε                             : Carrier
    isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid Carrier _•_ ε

  open IsIdempotentCommutativeMonoid isIdempotentCommutativeMonoid public

  commutativeMonoid : CommutativeMonoid _
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public
    using (magma; semigroup; monoid)

instance
  IdemCommMonoidCarrier : ∀ {c} → HasCarrier (IdempotentCommutativeMonoid c) c
  IdemCommMonoidCarrier = record { ⟨_⟩ = IdempotentCommutativeMonoid.Carrier }


-- Idempotent commutative monoids are also known as bounded lattices.
-- Note that the BoundedLattice necessarily uses the notation inherited
-- from monoids rather than lattices.

BoundedLattice = IdempotentCommutativeMonoid
pattern mkboundedlattice = mkidemcommmonoid

module BoundedLattice {c} (idemCommMonoid : IdempotentCommutativeMonoid c) =
       IdempotentCommutativeMonoid idemCommMonoid


------------------------------------------------------------------------
-- Bundles with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------

record Group c : Type (ℓ-suc c) where
  constructor mkgroup
  infix  8 _⁻¹
  infixl 7 _•_
  field
    Carrier : Type c
    _•_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isGroup : IsGroup Carrier _•_ ε _⁻¹

  open IsGroup isGroup public

  monoid : Monoid _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (magma; semigroup)

instance
  GroupCarrier : ∀ {c} → HasCarrier (Group c) c
  GroupCarrier = record { ⟨_⟩ = Group.Carrier }


record AbelianGroup c : Type (ℓ-suc c) where
  constructor mkabgroup
  infix  8 -_
  infixl 7 _+_
  field
    Carrier        : Type c
    _+_            : Op₂ Carrier
    ε              : Carrier
    -_             : Op₁ Carrier
    isAbelianGroup : IsAbelianGroup Carrier _+_ ε -_

  open IsAbelianGroup isAbelianGroup public

  group : Group _
  group = record { isGroup = isGroup }

  open Group group public
    using (magma; semigroup; monoid)

  commutativeMonoid : CommutativeMonoid _
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public
    using (commutativeSemigroup)

instance
  AbelianGroupCarrier : ∀ {c} → HasCarrier (AbelianGroup c) c
  AbelianGroupCarrier = record { ⟨_⟩ = AbelianGroup.Carrier }


------------------------------------------------------------------------
-- Bundles with 2 binary operations
------------------------------------------------------------------------

record Lattice c : Type (ℓ-suc c) where
  constructor mklattice
  infixr 7 _⋀_
  infixr 6 _⋁_
  field
    Carrier   : Type c
    _⋀_       : Op₂ Carrier
    _⋁_       : Op₂ Carrier
    isLattice : IsLattice Carrier _⋀_ _⋁_

  open IsLattice isLattice public

instance
  LatticeCarrier : ∀ {c} → HasCarrier (Lattice c) c
  LatticeCarrier = record { ⟨_⟩ = Lattice.Carrier }

record DistributiveLattice c : Type (ℓ-suc c) where
  constructor mkdistrlattice
  infixr 7 _⋀_
  infixr 6 _⋁_
  field
    Carrier               : Type c
    _⋀_                   : Op₂ Carrier
    _⋁_                   : Op₂ Carrier
    isDistributiveLattice : IsDistributiveLattice Carrier _⋀_ _⋁_

  open IsDistributiveLattice isDistributiveLattice public

  lattice : Lattice _
  lattice = record { isLattice = isLattice }

instance
  DistrLatticeCarrier : ∀ {c} → HasCarrier (DistributiveLattice c) c
  DistrLatticeCarrier = record { ⟨_⟩ = DistributiveLattice.Carrier }


------------------------------------------------------------------------
-- Bundles with 2 binary operations & 1 element
------------------------------------------------------------------------

record NearSemiring c : Type (ℓ-suc c) where
  constructor mknearsemiring
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier        : Type c
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    0#             : Carrier
    isNearSemiring : IsNearSemiring Carrier _+_ _*_ 0#

  open IsNearSemiring isNearSemiring public

  +-monoid : Monoid _
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
    using () renaming
    ( magma     to +-magma
    ; semigroup to +-semigroup
    )

  *-semigroup : Semigroup _
  *-semigroup = record { isSemigroup = *-isSemigroup }

  open Semigroup *-semigroup public
    using () renaming
    ( magma to *-magma )

instance
  NearSemiringCarrier : ∀ {c} → HasCarrier (NearSemiring c) c
  NearSemiringCarrier = record { ⟨_⟩ = NearSemiring.Carrier }


record SemiringWithoutOne c : Type (ℓ-suc c) where
  constructor mksemiringwo1
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier              : Type c
    _+_                  : Op₂ Carrier
    _*_                  : Op₂ Carrier
    0#                   : Carrier
    isSemiringWithoutOne : IsSemiringWithoutOne Carrier _+_ _*_ 0#

  open IsSemiringWithoutOne isSemiringWithoutOne public

  nearSemiring : NearSemiring _
  nearSemiring = record { isNearSemiring = isNearSemiring }

  open NearSemiring nearSemiring public
    using
    ( +-magma; +-semigroup; +-monoid
    ; *-magma; *-semigroup
    )

  +-commutativeMonoid : CommutativeMonoid _
  +-commutativeMonoid = record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
    using () renaming (commutativeSemigroup to +-commutativeSemigroup)

instance
  SemiringW1Carrier : ∀ {c} → HasCarrier (SemiringWithoutOne c) c
  SemiringW1Carrier = record { ⟨_⟩ = SemiringWithoutOne.Carrier }


record CommutativeSemiringWithoutOne c : Type (ℓ-suc c) where
  constructor mkcommsemiringwo1
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier                         : Type c
    _+_                             : Op₂ Carrier
    _*_                             : Op₂ Carrier
    0#                              : Carrier
    isCommutativeSemiringWithoutOne :
      IsCommutativeSemiringWithoutOne Carrier _+_ _*_ 0#

  open IsCommutativeSemiringWithoutOne
         isCommutativeSemiringWithoutOne public

  semiringWithoutOne : SemiringWithoutOne _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
    using
    ( +-magma; +-semigroup; +-commutativeSemigroup
    ; *-magma; *-semigroup
    ; +-monoid; +-commutativeMonoid
    ; nearSemiring
    )

instance
  CommSemiringW1Carrier : ∀ {c} → HasCarrier (CommutativeSemiringWithoutOne c) c
  CommSemiringW1Carrier = record { ⟨_⟩ = CommutativeSemiringWithoutOne.Carrier }


------------------------------------------------------------------------
-- Bundles with 2 binary operations & 2 elements
------------------------------------------------------------------------

record SemiringWithoutAnnihilatingZero c : Type (ℓ-suc c) where
  constructor mksemiringwoa0
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier                           : Type c
    _+_                               : Op₂ Carrier
    _*_                               : Op₂ Carrier
    0#                                : Carrier
    1#                                : Carrier
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero Carrier _+_ _*_ 0# 1#

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  +-commutativeMonoid : CommutativeMonoid _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
    using () renaming
    ( magma                to +-magma
    ; semigroup            to +-semigroup
    ; commutativeSemigroup to +-commutativeSemigroup
    ; monoid               to +-monoid
    )

  *-monoid : Monoid _
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
    using ()
    renaming
    ( magma     to *-magma
    ; semigroup to *-semigroup
    )

instance
  SemiringWA0Carrier : ∀ {c} → HasCarrier (SemiringWithoutAnnihilatingZero c) c
  SemiringWA0Carrier = record { ⟨_⟩ = SemiringWithoutAnnihilatingZero.Carrier }


record Semiring c : Type (ℓ-suc c) where
  constructor mksemiring
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier    : Type c
    _+_        : Op₂ Carrier
    _*_        : Op₂ Carrier
    0#         : Carrier
    1#         : Carrier
    isSemiring : IsSemiring Carrier _+_ _*_ 0# 1#

  open IsSemiring isSemiring public

  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _
  semiringWithoutAnnihilatingZero = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    }

  open SemiringWithoutAnnihilatingZero
         semiringWithoutAnnihilatingZero public
    using
    ( +-magma;  +-semigroup; +-commutativeSemigroup
    ; *-magma;  *-semigroup
    ; +-monoid; +-commutativeMonoid
    ; *-monoid
    )

  semiringWithoutOne : SemiringWithoutOne _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
    using (nearSemiring)

instance
  SemiringCarrier : ∀ {c} → HasCarrier (Semiring c) c
  SemiringCarrier = record { ⟨_⟩ = Semiring.Carrier }


record CommutativeSemiring c : Type (ℓ-suc c) where
  constructor mkcommsemiring
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier               : Type c
    _+_                   : Op₂ Carrier
    _*_                   : Op₂ Carrier
    0#                    : Carrier
    1#                    : Carrier
    isCommutativeSemiring : IsCommutativeSemiring Carrier _+_ _*_ 0# 1#

  open IsCommutativeSemiring isCommutativeSemiring public

  semiring : Semiring _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
    using
    ( +-magma; +-semigroup; +-commutativeSemigroup
    ; *-magma; *-semigroup
    ; +-monoid; +-commutativeMonoid
    ; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    )

  *-commutativeSemigroup : CommutativeSemigroup _
  *-commutativeSemigroup = record
    { isCommutativeSemigroup = *-isCommutativeSemigroup
    }

  *-commutativeMonoid : CommutativeMonoid _
  *-commutativeMonoid = record
    { isCommutativeMonoid = *-isCommutativeMonoid
    }

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _
  commutativeSemiringWithoutOne = record
    { isCommutativeSemiringWithoutOne = isCommutativeSemiringWithoutOne
    }

instance
  CommSemiringCarrier : ∀ {c} → HasCarrier (CommutativeSemiring c) c
  CommSemiringCarrier = record { ⟨_⟩ = CommutativeSemiring.Carrier }


------------------------------------------------------------------------
-- Bundles with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

record Ring c : Type (ℓ-suc c) where
  constructor mkring
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier : Type c
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    isRing  : IsRing Carrier _+_ _*_ -_ 0# 1#

  open IsRing isRing public

  +-abelianGroup : AbelianGroup _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  semiring : Semiring _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
    using
    ( +-magma; +-semigroup; +-commutativeSemigroup
    ; *-magma; *-semigroup
    ; +-monoid ; +-commutativeMonoid
    ; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    )

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group)

instance
  RingCarrier : ∀ {c} → HasCarrier (Ring c) c
  RingCarrier = record { ⟨_⟩ = Ring.Carrier }


record CommutativeRing c : Type (ℓ-suc c) where
  constructor mkcommring
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier           : Type c
    _+_               : Op₂ Carrier
    _*_               : Op₂ Carrier
    -_                : Op₁ Carrier
    0#                : Carrier
    1#                : Carrier
    isCommutativeRing : IsCommutativeRing Carrier _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  ring : Ring _
  ring = record { isRing = isRing }

  commutativeSemiring : CommutativeSemiring _
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open Ring ring public using (+-group; +-abelianGroup)
  open CommutativeSemiring commutativeSemiring public
    using
    ( +-magma; +-semigroup; +-commutativeSemigroup
    ; *-magma; *-semigroup; *-commutativeSemigroup
    ; +-monoid; +-commutativeMonoid
    ; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne
    )

instance
  CommRingCarrier : ∀ {c} → HasCarrier (CommutativeRing c) c
  CommRingCarrier = record { ⟨_⟩ = CommutativeRing.Carrier }


record BooleanAlgebra c : Type (ℓ-suc c) where
  constructor mkbooleanalgebra
  infix  8 ¬_
  infixr 7 _⋀_
  infixr 6 _⋁_
  field
    Carrier          : Type c
    _⋀_              : Op₂ Carrier
    _⋁_              : Op₂ Carrier
    ¬_               : Op₁ Carrier
    ⊤                : Carrier
    ⊥                : Carrier
    isBooleanAlgebra : IsBooleanAlgebra Carrier _⋀_ _⋁_ ¬_ ⊤ ⊥

  open IsBooleanAlgebra isBooleanAlgebra public

  distributiveLattice : DistributiveLattice _
  distributiveLattice = record { isDistributiveLattice = isDistributiveLattice }

  open DistributiveLattice distributiveLattice public
    using (lattice)

instance
  BooleanCarrier : ∀ {c} → HasCarrier (BooleanAlgebra c) c
  BooleanCarrier = record { ⟨_⟩ = BooleanAlgebra.Carrier }


------------------------------------------------------------------------
-- Bundles with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

record DivisionRing c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  constructor mkdivring
  infix  9 _⁻¹
  infix  8 -_
  infixr 7 _*_
  infixr 6 _+_
  field
    Carrier        : Type c
    Invertible     : Carrier → Type ℓ
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    0#             : Carrier
    1#             : Carrier
    -_             : Op₁ Carrier
    _⁻¹            : Σ Carrier Invertible → Carrier
    isDivisionRing : IsDivisionRing Carrier Invertible _+_ _*_ -_ _⁻¹ 0# 1#

  open IsDivisionRing isDivisionRing public

  ring : Ring _
  ring = record { isRing = isRing }

  open Ring ring public using (+-group; +-abelianGroup)

instance
  DivisionRingCarrier : ∀ {c ℓ} → HasCarrier (DivisionRing c ℓ) c
  DivisionRingCarrier = record { ⟨_⟩ = DivisionRing.Carrier }


record Field c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  constructor mkfield
  infix  9 _⁻¹
  infix  8 -_
  infixr 7 _*_
  infixr 6 _+_
  field
    Carrier    : Type c
    Invertible : Carrier → Type ℓ
    _+_        : Op₂ Carrier
    _*_        : Op₂ Carrier
    0#         : Carrier
    1#         : Carrier
    -_         : Op₁ Carrier
    _⁻¹        : Σ Carrier Invertible → Carrier
    isField    : IsField Carrier Invertible _+_ _*_ -_ _⁻¹ 0# 1#

  open IsField isField public

  divisionRing : DivisionRing _ _
  divisionRing = record { isDivisionRing = isDivisionRing }

  open DivisionRing divisionRing public using (ring; +-group; +-abelianGroup)

  commutativeRing : CommutativeRing _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  open CommutativeRing commutativeRing public
      using
      ( commutativeSemiring
      ; +-magma; +-semigroup; +-commutativeSemigroup
      ; *-magma; *-semigroup; *-commutativeSemigroup
      ; +-monoid; +-commutativeMonoid
      ; *-monoid; *-commutativeMonoid
      ; nearSemiring; semiringWithoutOne
      ; semiringWithoutAnnihilatingZero; semiring
      ; commutativeSemiringWithoutOne
      )

instance
  FieldCarrier : ∀ {c ℓ} → HasCarrier (Field c ℓ) c
  FieldCarrier = record { ⟨_⟩ = Field.Carrier }
