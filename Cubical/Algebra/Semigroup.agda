{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup where

open import Cubical.Algebra.Base public
open import Cubical.Algebra.Definitions public

open import Cubical.Algebra.Structures public using (IsSemigroup; issemigroup)
open import Cubical.Algebra.Bundles public using (Semigroup; mksemigroup; SemigroupCarrier)
open import Cubical.Structures.Carrier public

open import Cubical.Algebra.Semigroup.Properties public
open import Cubical.Algebra.Semigroup.Morphism public
open import Cubical.Algebra.Semigroup.MorphismProperties public hiding (isPropIsSemigroup)
