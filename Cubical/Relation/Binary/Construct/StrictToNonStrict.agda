{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary

module Cubical.Relation.Binary.Construct.StrictToNonStrict
  {a ℓ} {A : Type a}
  (_<_ : Rel A ℓ)
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Logic hiding (_⇒_) renaming (inl to inlₚ; inr to inrₚ)

open import Cubical.Data.Prod
open import Cubical.Data.Sum.Base renaming (rec to ⊎-rec)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) using (isProp⊥)
open import Cubical.Relation.Binary.Properties
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT

------------------------------------------------------------------------
-- Conversion

-- _<_ can be turned into _≤_ as follows:

_≤_ : Rel A _
x ≤ y = (x < y) ⊔ (x ≡ₚ y)

------------------------------------------------------------------------
-- The converted relations have certain properties
-- (if the original relations have certain other properties)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = inlₚ

≤-fromEq : FromEq _≤_
≤-fromEq = inrₚ

≤-reflexive : Reflexive _≤_
≤-reflexive = fromeq→reflx _≤_ ≤-fromEq

≤-antisym : Transitive _<_ → Irreflexive _<_ → Antisymmetric _≤_
≤-antisym transitive irrefl = rec2 squash λ
  { (inl x) (inl y) → ⊥-elim (irrefl (transitive x y))
  ; (inl x) (inr y) → PT.map sym y
  ; (inr x) _ → x
  }

≤-transitive : Transitive _<_ → Transitive _≤_
≤-transitive <-trans = rec2 squash λ
  { (inl x) (inl y) → inlₚ (<-trans x y)
  ; (inl x) (inr y) → inlₚ (substₚ (λ k → _ < k) y x)
  ; (inr x) (inl y) → inlₚ (substₚ (λ i → i < _) (PT.map sym x) y)
  ; (inr x) (inr y) → inrₚ (PT.map2 _∙_ x y)
  }

<-≤-trans : Transitive _<_ → Trans _<_ _≤_ _<_
<-≤-trans transitive x<y = rec (isProp[ _<_ ] _ _) λ
  { (inl x) → transitive x<y x
  ; (inr x) → substₚ (λ k → _ < k) x x<y
  }

≤-<-trans : Transitive _<_ → Trans _≤_ _<_ _<_
≤-<-trans transitive = rec (isPropΠ λ _ → isProp[ _<_ ] _ _) λ
  { (inl x) y → transitive x y
  ; (inr x) y → substₚ (λ i → i < _) (PT.map sym x) y
  }

≤-total : Trichotomous _<_ → Total _≤_
≤-total <-tri x y with <-tri x y
... | tri< x<y x≢y x≯y = inlₚ (inlₚ x<y)
... | tri≡ x≮y x≡y x≯y = inlₚ (inrₚ ∣ x≡y ∣)
... | tri> x≮y x≢y x>y = inrₚ (inlₚ x>y)

≤-decidable : Discrete A → Decidable _<_ → Decidable _≤_
≤-decidable _≟_ _<?_ x y with x <? y
... | yes x<y = yes (inlₚ x<y)
... | no x≮y with x ≟ y
... |    yes x≡y = yes (inrₚ ∣ x≡y ∣)
... |    no x≢y = no (rec isProp⊥ λ
                    { (inl x<y) → x≮y x<y
                    ; (inr x≡y) → x≢y (rec (Discrete→isSet _≟_ _ _) id x≡y)
                    })

≤-decidable′ : Trichotomous _<_ → Decidable _≤_
≤-decidable′ compare x y with compare x y
... | tri< x<y x≢y x≯y = yes (inlₚ x<y)
... | tri≡ x≮y x≡y x≯y = yes (inrₚ ∣ x≡y ∣)
... | tri> x≮y x≢y x>y = no (rec isProp⊥ λ
                          { (inl x<y) → x≮y x<y
                          ; (inr x≡y) → x≢y (rec (Discrete→isSet (tri→dec≡ _<_ compare) _ _) id x≡y)
                          })

------------------------------------------------------------------------
-- Converting structures

isPreorder : Transitive _<_ → IsPreorder _≤_
isPreorder transitive = record
  { reflexive  = ≤-reflexive
  ; transitive = ≤-transitive transitive
  }

isPartialOrder : IsStrictPartialOrder _<_ → IsPartialOrder _≤_
isPartialOrder spo = record
  { isPreorder = isPreorder S.transitive
  ; antisym    = ≤-antisym S.transitive S.irrefl
  }
  where module S = IsStrictPartialOrder spo

isTotalOrder : IsStrictTotalOrder _<_ → IsTotalOrder _≤_
isTotalOrder sto = record
  { isPartialOrder = isPartialOrder S.isStrictPartialOrder
  ; total          = ≤-total S.compare
  }
  where module S = IsStrictTotalOrder sto

isDecTotalOrder : IsStrictTotalOrder _<_ → IsDecTotalOrder _≤_
isDecTotalOrder sto = record
  { isTotalOrder = isTotalOrder sto
  ; _≤?_         = ≤-decidable′ S.compare
  }
  where module S = IsStrictTotalOrder sto
