{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Construct.Never where

open import Cubical.Core.Everything

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Construct.Constant
open import Cubical.Data.Empty.Polymorphic

------------------------------------------------------------------------
-- Definition

Never : ∀ {a b ℓ} {A : Type a} {B : Type b} → REL A B ℓ
Never = Const (⊥ , isProp⊥)
