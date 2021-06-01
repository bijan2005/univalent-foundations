------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for reasoning with a partial setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.PartialEquivalence
  {c ℓ} {A : Type c} (E : PartialEquivalence A ℓ) where

open PartialEquivalence E
import Cubical.Relation.Binary.Reasoning.Base.Partial _≈_ transitive as Base

------------------------------------------------------------------------
-- Re-export the contents of the base module

open Base public
  renaming (_∼⟨_⟩_ to _≈⟨_⟩_)

------------------------------------------------------------------------
-- Additional reasoning combinators

infixr 1 _≈˘⟨_⟩_

_≈˘⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
x ≈˘⟨ y≈x ⟩ y∼z = x ≈⟨ symmetric y≈x ⟩ y∼z
