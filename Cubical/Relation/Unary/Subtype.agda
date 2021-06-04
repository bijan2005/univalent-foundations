{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Unary.Subtype where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Unary
open import Cubical.Data.Nat

private
  variable
    a ℓ ℓ′ : Level
    A : Type a

Subtype : (P : Pred A ℓ) → Type _
Subtype {A = A} P = Σ[ x ∈ A ] x ∈ P

module _ (P : Pred A ℓ) where

  isOfHLevelSubtype : ∀ n → isOfHLevel (suc n) A → isOfHLevel (suc n) (Subtype P)
  isOfHLevelSubtype n hA = isOfHLevelΣ (suc n) hA (λ _ → isProp→isOfHLevelSuc n (isProp[ P ] _))

  isSetSubtype : isSet A → isSet (Subtype P)
  isSetSubtype = isOfHLevelSubtype 1


inclusion : (P : Pred A ℓ) (Q : Pred A ℓ′) → P ⊆ Q → Subtype P → Subtype Q
inclusion P Q P⊆Q = λ (x , Px) → (x , P⊆Q Px)

⇔-equiv : (P : Pred A ℓ) (Q : Pred A ℓ′) → P ⇔ Q → Subtype P ≃ Subtype Q
⇔-equiv P Q (P⊆Q , Q⊆P) = isoToEquiv (iso (inclusion P Q P⊆Q) (inclusion Q P Q⊆P)
                                            (λ (x , Qx) → cong (x ,_) (Q x .snd _ _))
                                            (λ (x , Px) → cong (x ,_) (P x .snd _ _))
                                       )
