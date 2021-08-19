{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Subgroup where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Algebra
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Monoid.Submonoid

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype

open import Cubical.HITs.PropositionalTruncation


record IsSubgroup {c ℓ} (G : Group c) (Member : Pred ⟨ G ⟩ ℓ) : Type (ℓ-max c ℓ) where
  constructor issubgroup

  private module G = Group G

  field
    preservesOp : G._•_ Preserves₂ Member
    preservesInv : G._⁻¹ Preserves Member
    preservesId : G.ε ∈ Member


  isSubmonoid : IsSubmonoid G.monoid Member
  isSubmonoid = record
    { preservesOp = preservesOp
    ; preservesId = preservesId
    }

  open IsSubmonoid isSubmonoid hiding (preservesOp; preservesId; _^_) public

  _⁻¹ : Op₁ Carrier
  (x , subx) ⁻¹ = x G.⁻¹ , preservesInv subx

  inverseˡ : LeftInverse ε _⁻¹ _•_
  inverseˡ _ = ΣPathTransport→PathΣ _ _ (G.inverseˡ _ , isProp[ Member ] _ _ _)

  inverseʳ : RightInverse ε _⁻¹ _•_
  inverseʳ _ = ΣPathTransport→PathΣ _ _ (G.inverseʳ _ , isProp[ Member ] _ _ _)

  inverse : Inverse ε _⁻¹ _•_
  inverse = inverseˡ , inverseʳ


  isGroup : IsGroup Carrier _•_ ε _⁻¹
  isGroup = record
    { isMonoid = isMonoid
    ; inverse = inverse
    }

  group : Group _
  group = record { isGroup = isGroup }

  open Group group using
    ( _^_
    ; _/_
    ; _/ˡ_
    ; inv-uniqueˡ
    ; inv-uniqueʳ
    ; cancelˡ
    ; cancelʳ
    ) public


record Subgroup {c} (G : Group c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubgroup

  private module G = Group G

  field
    Member : Pred ⟨ G ⟩ ℓ
    isSubgroup : IsSubgroup G Member

  open IsSubgroup isSubgroup public

  submonoid : Submonoid G.monoid ℓ
  submonoid = record { isSubmonoid = isSubmonoid }

  open Submonoid submonoid using (submagma; subsemigroup)


instance
  SubgroupCarrier : ∀ {c ℓ} {G : Group c} → HasCarrier (Subgroup G ℓ) _
  SubgroupCarrier = record { ⟨_⟩ = Subgroup.Carrier }


module _ {ℓ} (G : Group ℓ) where
  open Group G

  ε-isSubgroup : IsSubgroup G ｛ ε ｝
  ε-isSubgroup = record
    { preservesOp = map2 λ p q → cong₂ _•_ p q ∙ identityʳ ε
    ; preservesInv = map λ p → cong _⁻¹ p ∙ cancelʳ ε (inverseˡ ε ∙ sym (identityʳ ε))
    ; preservesId = ∣ refl ∣
    }

  ε-subgroup : Subgroup G _
  ε-subgroup = record { isSubgroup = ε-isSubgroup }

  U-isSubgroup : IsSubgroup G U
  U-isSubgroup = record {} -- trivial

  U-subgroup : Subgroup G _
  U-subgroup = record { isSubgroup = U-isSubgroup }
