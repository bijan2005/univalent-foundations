{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.Base.Single {a ℓ} {A : Type a}
  (_∼_ : RawRel A ℓ) (isPreorder : IsPreorder _∼_)
  where

open IsPreorder isPreorder

------------------------------------------------------------------------
-- Reasoning combinators

-- Re-export combinators from partial reasoning

open import Cubical.Relation.Binary.Reasoning.Base.Partial _∼_ transitive public
  hiding (_∎⟨_⟩)

-- Redefine the terminating combinator now that we have reflexivity

infix 2 _∎

_∎ : ∀ x → x ∼ x
x ∎ = reflexive
