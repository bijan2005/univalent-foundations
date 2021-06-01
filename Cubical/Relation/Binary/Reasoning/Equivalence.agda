{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.Equivalence {c ℓ} {A : Type c} (E : Equivalence A ℓ) where

open Equivalence E

------------------------------------------------------------------------
-- Reasoning combinators

open import Cubical.Relation.Binary.Reasoning.PartialEquivalence partialEquivalence public
  hiding (_∎⟨_⟩)
open import Cubical.Relation.Binary.Reasoning.Base.Single _≈_ isPreorder public
  using (_∎)
