{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma.Submagma where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra
open import Cubical.Algebra.Magma.Morphism

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype


record IsSubmagma {c ℓ} (M : Magma c) (Member : Pred ⟨ M ⟩ ℓ) : Type (ℓ-max c ℓ) where
  constructor issubmagma

  private module M = Magma M

  field
    closed : M._•_ Preserves₂ Member


  Carrier : Type _
  Carrier = Subtype Member

  _•_ : Op₂ Carrier
  (x , subx) • (y , suby) = x M.• y , closed subx suby

  is-set : isSet Carrier
  is-set = isSetSubtype Member M.is-set


  isMagma : IsMagma Carrier _•_
  isMagma = record { is-set = is-set }

  magma : Magma _
  magma = record { isMagma = isMagma }

  open Magma magma using (set) public


record Submagma {c} (M : Magma c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubmagma

  field
    Member : Pred ⟨ M ⟩ ℓ
    isSubmagma : IsSubmagma M Member

  open IsSubmagma isSubmagma public


instance
  SubmagmaCarrier : ∀ {c ℓ} {M : Magma c} → HasCarrier (Submagma M ℓ) _
  SubmagmaCarrier = record { ⟨_⟩ = Submagma.Carrier }


module _ {ℓ} (M : Magma ℓ) where
  open Magma M

  ∅-isSubmagma : IsSubmagma M ∅
  ∅-isSubmagma = record { closed = λ () }

  ∅-submagma : Submagma M _
  ∅-submagma = record { isSubmagma = ∅-isSubmagma }

  U-isSubmagma : IsSubmagma M U
  U-isSubmagma = record {} -- trivial

  U-submagma : Submagma M _
  U-submagma = record { isSubmagma = U-isSubmagma }


isPropIsSubmagma : ∀ {c ℓ} {M : Magma c} {Member : Pred ⟨ M ⟩ ℓ} → isProp (IsSubmagma M Member)
isPropIsSubmagma {Member = Member} (issubmagma a) (issubmagma b) =
  cong issubmagma ((isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ2 λ _ _ → isProp[ Member ] _) a b)
