{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding

open import Cubical.Algebra
open import Cubical.Algebra.Magma.Morphism

private
  variable
    s t : Level

IsSemigroupHom : (S : Semigroup s) (T : Semigroup t) → (⟨ S ⟩ → ⟨ T ⟩) → Type (ℓ-max s t)
IsSemigroupHom S T fun = Homomorphic₂ fun (Semigroup._•_ S) (Semigroup._•_ T)

record SemigroupHom (S : Semigroup s) (T : Semigroup t) : Type (ℓ-max s t) where
  constructor semigrouphom
  field
    fun : ⟨ S ⟩ → ⟨ T ⟩
    isHom : IsSemigroupHom S T fun

record SemigroupEquiv (S : Semigroup s) (T : Semigroup t) : Type (ℓ-max s t) where
  constructor semigroupequiv
  field
    eq : ⟨ S ⟩ ≃ ⟨ T ⟩
    isHom : IsSemigroupHom S T (equivFun eq)

  hom : SemigroupHom S T
  hom = record { isHom = isHom }


private
  variable
    S : Semigroup s
    T : Semigroup t


SemigroupHom→MagmaHom : SemigroupHom S T → MagmaHom (Semigroup.magma S) (Semigroup.magma T)
SemigroupHom→MagmaHom hom .MagmaHom.fun = hom .SemigroupHom.fun
SemigroupHom→MagmaHom hom .MagmaHom.isHom = hom .SemigroupHom.isHom

MagmaHom→SemigroupHom : MagmaHom (Semigroup.magma S) (Semigroup.magma T) → SemigroupHom S T
MagmaHom→SemigroupHom hom .SemigroupHom.fun = hom .MagmaHom.fun
MagmaHom→SemigroupHom hom .SemigroupHom.isHom = hom .MagmaHom.isHom

SemigroupHom≃MagmaHom : SemigroupHom S T ≃ MagmaHom (Semigroup.magma S) (Semigroup.magma T)
SemigroupHom≃MagmaHom = isoToEquiv (iso SemigroupHom→MagmaHom MagmaHom→SemigroupHom (λ _ → refl) (λ _ → refl))


SemigroupEquiv→MagmaEquiv : SemigroupEquiv S T → MagmaEquiv (Semigroup.magma S) (Semigroup.magma T)
SemigroupEquiv→MagmaEquiv eq .MagmaEquiv.eq = eq .SemigroupEquiv.eq
SemigroupEquiv→MagmaEquiv eq .MagmaEquiv.isHom = eq .SemigroupEquiv.isHom

MagmaEquiv→SemigroupEquiv : MagmaEquiv (Semigroup.magma S) (Semigroup.magma T) → SemigroupEquiv S T
MagmaEquiv→SemigroupEquiv eq .SemigroupEquiv.eq = eq .MagmaEquiv.eq
MagmaEquiv→SemigroupEquiv eq .SemigroupEquiv.isHom = eq .MagmaEquiv.isHom

SemigroupEquiv≃MagmaEquiv : SemigroupEquiv S T ≃ MagmaEquiv (Semigroup.magma S) (Semigroup.magma T)
SemigroupEquiv≃MagmaEquiv = isoToEquiv (iso SemigroupEquiv→MagmaEquiv MagmaEquiv→SemigroupEquiv (λ _ → refl) (λ _ → refl))
