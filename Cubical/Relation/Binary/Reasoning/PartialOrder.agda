{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.PartialOrder
  {c ℓ} {A : Type c} (P : PartialOrder A ℓ) where

open PartialOrder P
import Cubical.Relation.Binary.Raw.Construct.NonStrictToStrict _≤_ as Strict

------------------------------------------------------------------------
-- Re-export contents of base module

open import Cubical.Relation.Binary.Reasoning.Base.Double
  isPreorder
  (Strict.<-transitive isPartialOrder)
  Strict.<⇒≤
  (Strict.<-≤-trans transitive antisym)
  (Strict.≤-<-trans transitive antisym)
  public
