{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Reasoning.Preorder {c ℓ} {A : Type c} (P : Preorder A ℓ) where

open Preorder P

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Cubical.Relation.Binary.Reasoning.Base.Single _∼_ isPreorder public
