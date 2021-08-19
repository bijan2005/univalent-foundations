{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.Subsemigroup where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Algebra
open import Cubical.Algebra.Semigroup.Morphism
open import Cubical.Algebra.Magma.Submagma

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype


record IsSubsemigroup {c ℓ} (S : Semigroup c) (Member : Pred ⟨ S ⟩ ℓ) : Type (ℓ-max c ℓ) where
  constructor issubsemigroup

  private module S = Semigroup S

  field
    closed : S._•_ Preserves₂ Member


  isSubmagma : IsSubmagma S.magma Member
  isSubmagma = record { closed = closed }

  open IsSubmagma isSubmagma hiding (closed) public


  assoc : Associative _•_
  assoc _ _ _ = ΣPathTransport→PathΣ _ _ (S.assoc _ _ _ , isProp[ Member ] _ _ _)


  isSemigroup : IsSemigroup Carrier _•_
  isSemigroup = record
    { isMagma = isMagma
    ; assoc = assoc
    }

  semigroup : Semigroup _
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup using (_^_) public


record Subsemigroup {c} (S : Semigroup c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubsemigroup

  private module S = Semigroup S

  field
    Member : Pred ⟨ S ⟩ ℓ
    isSubsemigroup : IsSubsemigroup S Member

  open IsSubsemigroup isSubsemigroup public

  submagma : Submagma S.magma ℓ
  submagma = record { isSubmagma = isSubmagma }


instance
  SubsemigroupCarrier : ∀ {c ℓ} {S : Semigroup c} → HasCarrier (Subsemigroup S ℓ) _
  SubsemigroupCarrier = record { ⟨_⟩ = Subsemigroup.Carrier }


module _ {ℓ} (S : Semigroup ℓ) where
  open Semigroup S

  ∅-isSubsemigroup : IsSubsemigroup S ∅
  ∅-isSubsemigroup = record { closed = λ () }

  ∅-subsemigroup : Subsemigroup S _
  ∅-subsemigroup = record { isSubsemigroup = ∅-isSubsemigroup }

  U-isSubsemigroup : IsSubsemigroup S U
  U-isSubsemigroup = record {} -- trivial

  U-subsemigroup : Subsemigroup S _
  U-subsemigroup = record { isSubsemigroup = U-isSubsemigroup }
