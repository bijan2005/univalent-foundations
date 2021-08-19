{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Monoid.Submonoid where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Algebra
open import Cubical.Algebra.Monoid.Morphism
open import Cubical.Algebra.Semigroup.Subsemigroup

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype

open import Cubical.HITs.PropositionalTruncation


record IsSubmonoid {c ℓ} (M : Monoid c) (Member : Pred ⟨ M ⟩ ℓ) : Type (ℓ-max c ℓ) where
  constructor issubmonoid

  private module M = Monoid M

  field
    preservesOp : M._•_ Preserves₂ Member
    preservesId : M.ε ∈ Member

  isSubsemigroup : IsSubsemigroup M.semigroup Member
  isSubsemigroup = record { closed = preservesOp }

  open IsSubsemigroup isSubsemigroup hiding (closed; _^_) public


  ε : Carrier
  ε = M.ε , preservesId

  identityˡ : LeftIdentity ε _•_
  identityˡ _ = ΣPathTransport→PathΣ _ _ (M.identityˡ _ , isProp[ Member ] _ _ _)

  identityʳ : RightIdentity ε _•_
  identityʳ _ = ΣPathTransport→PathΣ _ _ (M.identityʳ _ , isProp[ Member ] _ _ _)

  identity : Identity ε _•_
  identity = identityˡ , identityʳ


  isMonoid : IsMonoid Carrier _•_ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity = identity
    }

  monoid : Monoid _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid using (ε-uniqueˡ; ε-uniqueʳ; _^_) public




record Submonoid {c} (M : Monoid c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubmonoid

  private module M = Monoid M

  field
    Member : Pred ⟨ M ⟩ ℓ
    isSubmonoid : IsSubmonoid M Member

  open IsSubmonoid isSubmonoid public

  subsemigroup : Subsemigroup M.semigroup ℓ
  subsemigroup = record { isSubsemigroup = isSubsemigroup }

  open Subsemigroup subsemigroup public using (submagma)


instance
  SubmonoidCarrier : ∀ {c ℓ} {M : Monoid c} → HasCarrier (Submonoid M ℓ) _
  SubmonoidCarrier = record { ⟨_⟩ = Submonoid.Carrier }


module _ {ℓ} (M : Monoid ℓ) where
  open Monoid M

  ε-isSubmonoid : IsSubmonoid M ｛ ε ｝
  ε-isSubmonoid = record
    { preservesOp = map2 λ p q → cong₂ _•_ p q ∙ identityʳ ε
    ; preservesId = ∣ refl ∣
    }

  ε-submonoid : Submonoid M _
  ε-submonoid = record { isSubmonoid = ε-isSubmonoid }

  U-isSubmonoid : IsSubmonoid M U
  U-isSubmonoid = record {} -- trivial

  U-submonoid : Submonoid M _
  U-submonoid = record { isSubmonoid = U-isSubmonoid }
