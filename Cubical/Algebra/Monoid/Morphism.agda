{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Monoid.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding

open import Cubical.Algebra
open import Cubical.Algebra.Semigroup.Morphism

private
  variable
    m n : Level

record IsMonoidHom (M : Monoid m) (N : Monoid n) (f : ⟨ M ⟩ → ⟨ N ⟩) : Type (ℓ-max m n) where
  constructor ismonoidhom
  field
    preservesOp : Homomorphic₂ f (Monoid._•_ M) (Monoid._•_ N)
    preservesId : Homomorphic₀ f (Monoid.ε M)   (Monoid.ε N)

record MonoidHom (M : Monoid m) (N : Monoid n) : Type (ℓ-max m n) where
  constructor monoidhom
  field
    fun : ⟨ M ⟩ → ⟨ N ⟩
    isHom : IsMonoidHom M N fun

  open IsMonoidHom isHom public

record MonoidEquiv (M : Monoid m) (N : Monoid n) : Type (ℓ-max m n) where
  constructor monoidequiv
  field
    eq : ⟨ M ⟩ ≃ ⟨ N ⟩
    isHom : IsMonoidHom M N (equivFun eq)

  open IsMonoidHom isHom public

  hom : MonoidHom M N
  hom = record { isHom = isHom }


private
  variable
    M : Monoid m
    N : Monoid n

IsMonoidHom→IsSemigroupHom : {f : ⟨ M ⟩ → ⟨ N ⟩} → IsMonoidHom M N f → IsSemigroupHom (Monoid.semigroup M) (Monoid.semigroup N) f
IsMonoidHom→IsSemigroupHom = IsMonoidHom.preservesOp

MonoidHom→SemigroupHom : MonoidHom M N → SemigroupHom (Monoid.semigroup M) (Monoid.semigroup N)
MonoidHom→SemigroupHom hom .SemigroupHom.fun = hom .MonoidHom.fun
MonoidHom→SemigroupHom hom .SemigroupHom.isHom = IsMonoidHom→IsSemigroupHom (hom .MonoidHom.isHom)

MonoidEquiv→SemigroupEquiv : MonoidEquiv M N → SemigroupEquiv (Monoid.semigroup M) (Monoid.semigroup N)
MonoidEquiv→SemigroupEquiv eq .SemigroupEquiv.eq = eq .MonoidEquiv.eq
MonoidEquiv→SemigroupEquiv eq .SemigroupEquiv.isHom = IsMonoidHom→IsSemigroupHom (eq .MonoidEquiv.isHom)
