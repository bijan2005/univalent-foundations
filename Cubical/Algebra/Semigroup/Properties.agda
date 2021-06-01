{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Semigroup.Morphism
open import Cubical.Algebra.Magma.Properties using (isPropIsMagma)

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Reasoning.Equality

open import Cubical.Algebra.Semigroup.MorphismProperties public
  using (SemigroupPath; uaSemigroup; carac-uaSemigroup; Semigroup≡; caracSemigroup≡)

private
  variable
    ℓ ℓ′ : Level


isPropIsSemigroup : ∀ {S : Type ℓ} {_•_} → isProp (IsSemigroup S _•_)
isPropIsSemigroup {_} {_} {_•_} (issemigroup aMagma aAssoc) (issemigroup bMagma bAssoc) =
  cong₂ issemigroup (isPropIsMagma aMagma bMagma) (isPropAssociative (IsMagma.is-set aMagma) _•_ aAssoc bAssoc)


module SemigroupLemmas (S : Semigroup ℓ) where
  open Semigroup S

  ^-suc : ∀ x n → x ^ suc₊₁ n ≡ x ^ n • x
  ^-suc x one    = refl
  ^-suc x (2+ n) =
    x ^ suc₊₁ (2+ n)     ≡⟨⟩
    x ^ 1+ suc (suc n)   ≡⟨⟩
    x • (x • x ^ 1+ n)   ≡⟨⟩
    x • x ^ suc₊₁ (1+ n) ≡⟨ cong (x •_) (^-suc x (1+ n)) ⟩
    x • (x ^ 1+ n • x)   ≡˘⟨ assoc x (x ^ 1+ n) x ⟩
    x • x ^ 1+ n • x     ≡⟨⟩
    x ^ 2+ n • x         ∎

  ^-plus : ∀ x → Homomorphic₂ (x ^_) _+₊₁_ _•_
  ^-plus _ one _ = refl
  ^-plus x (2+ m) n =
    x ^ (1+ (suc m) +₊₁ n) ≡⟨⟩
    x • (x ^ (1+ m +₊₁ n)) ≡⟨ cong (x •_) (^-plus x (1+ m) n) ⟩
    x • (x ^ 1+ m • x ^ n) ≡˘⟨ assoc x (x ^ 1+ m) (x ^ n) ⟩
    x • x ^ 1+ m • x ^ n   ≡⟨⟩
    x ^ 2+ m • x ^ n       ∎


module Kernel {S : Semigroup ℓ} {T : Semigroup ℓ′} (hom : SemigroupHom S T) where
  private
    module S = Semigroup S
    module T = Semigroup T
  open SemigroupHom hom renaming (fun to f)

  Kernel : Rel ⟨ S ⟩ ℓ′
  Kernel x y = f x ≡ f y

  isPropKernel : isPropValued Kernel
  isPropKernel x y = T.is-set (f x) (f y)

  Kernelᴾ : PropRel ⟨ S ⟩ ℓ′
  Kernelᴾ = Kernel , isPropKernel


  ker-reflexive : Reflexive Kernel
  ker-reflexive = refl

  ker-fromEq : FromEq Kernel
  ker-fromEq = cong f

  ker-symmetric : Symmetric Kernel
  ker-symmetric = sym

  ker-transitive : Transitive Kernel
  ker-transitive = _∙_


  ker-isPreorder : IsPreorder Kernel
  ker-isPreorder = record
    { reflexive  = ker-reflexive
    ; transitive = ker-transitive
    }

  ker-isPartialEquivalence : IsPartialEquivalence Kernel
  ker-isPartialEquivalence = record
    { symmetric  = ker-symmetric
    ; transitive = ker-transitive
    }

  ker-isEquivalence : IsEquivalence Kernel
  ker-isEquivalence = record
    { isPartialEquivalence = ker-isPartialEquivalence
    ; reflexive            = ker-reflexive
    }


  ker⇒id→emb : Kernel ⇒ _≡_ → isEmbedding f
  ker⇒id→emb ker⇒id = injEmbedding S.is-set T.is-set ker⇒id

  emb→ker⇒id : isEmbedding f → Kernel ⇒ _≡_
  emb→ker⇒id isemb {x} {y} = invIsEq (isemb x y)
