{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.StrictPartialOrder
  {a ℓ} {A : Type a} (S : StrictPartialOrder A ℓ) where

open StrictPartialOrder S
import Cubical.Relation.Binary.Raw.Construct.StrictToNonStrict _<_ as NonStrict

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Cubical.Relation.Binary.Reasoning.Base.Double
  (NonStrict.isPreorder transitive)
  transitive
  NonStrict.<⇒≤
  (NonStrict.<-≤-trans transitive)
  public
