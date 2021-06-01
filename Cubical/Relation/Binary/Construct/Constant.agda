{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Construct.Constant where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)

open import Cubical.Relation.Binary
open import Cubical.Structures.Carrier

------------------------------------------------------------------------
-- Definition

Const : ∀ {a b ℓ} {A : Type a} {B : Type b} → hProp ℓ → REL A B ℓ
Const I = λ _ _ → I

------------------------------------------------------------------------
-- Properties

module _ {a c} {A : Type a} {C : hProp c} where

  reflexive : ⟨ C ⟩ → Reflexive {A = A} (Const C)
  reflexive c = c

  symmetric : Symmetric {A = A} (Const C)
  symmetric c = c

  transitive : Transitive {A = A} (Const C)
  transitive c d = c

  isPartialEquivalence : IsPartialEquivalence {A = A} (Const C)
  isPartialEquivalence = record
    { symmetric  = λ {x} {y} → symmetric {x} {y}
    ; transitive = λ {x} {y} {z} → transitive {x} {y} {z}
    }

  partialEquivalence : PartialEquivalence A c
  partialEquivalence = record { isPartialEquivalence = isPartialEquivalence }

  isEquivalence : ⟨ C ⟩ → IsEquivalence {A = A} (Const C)
  isEquivalence c = record
    { isPartialEquivalence = isPartialEquivalence
    ; reflexive            = λ {x} → reflexive c {x}
    }

  equivalence : ⟨ C ⟩ → Equivalence A c
  equivalence x = record { isEquivalence = isEquivalence x }
