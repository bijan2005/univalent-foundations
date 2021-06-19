{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma where

open import Cubical.Algebra.Base public
open import Cubical.Algebra.Definitions public

open import Cubical.Algebra.Structures public using (IsMagma; ismagma)
open import Cubical.Algebra.Bundles public using (Magma; mkmagma; MagmaCarrier)
open import Cubical.Structures.Carrier public

open import Cubical.Algebra.Magma.Properties public
open import Cubical.Algebra.Magma.Morphism public
open import Cubical.Algebra.Magma.MorphismProperties public
