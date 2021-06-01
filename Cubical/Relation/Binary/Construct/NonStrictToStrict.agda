{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary

module Cubical.Relation.Binary.Construct.NonStrictToStrict
  {a ℓ} {A : Type a} (_≤_ : Rel A ℓ) where

open import Cubical.Relation.Binary.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic hiding (_⇒_; ¬_)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Data.Empty
open import Cubical.Foundations.Function using (_∘_; flip; id)
open import Cubical.Relation.Nullary
import Cubical.HITs.PropositionalTruncation as PT


------------------------------------------------------------------------
-- _≤_ can be turned into _<_ as follows:

_<_ : Rel A _
x < y = x ≤ y ⊓ x ≢ₚ y

------------------------------------------------------------------------
-- Relationship between relations

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = fst

<⇒≢ : _<_ ⇒ _≢ₚ_
<⇒≢ = snd

≤∧≢⇒< : ∀ {x y} → ⟨ x ≤ y ⟩ → ⟨ x ≢ₚ y ⟩ → ⟨ x < y ⟩
≤∧≢⇒< = _,_

<⇒≱ : Antisymmetric _≤_ → ∀ {x y} → ⟨ x < y ⟩ → ¬ ⟨ y ≤ x ⟩
<⇒≱ antisym (x≤y , x≢y) y≤x = x≢y (antisym x≤y y≤x)

≤⇒≯ : Antisymmetric _≤_ → ∀ {x y} → ⟨ x ≤ y ⟩ → ¬ ⟨ y < x ⟩
≤⇒≯ antisym x≤y y<x = <⇒≱ antisym y<x x≤y

≰⇒> : Reflexive _≤_ → Total _≤_ →
      ∀ {x y} → ¬ ⟨ x ≤ y ⟩ → ⟨ y < x ⟩
≰⇒> rfl total {x} {y} x≰y = PT.rec ((y < x) .snd) (λ {
    (inl x≤y) → elim (x≰y x≤y)
  ; (inr y≤x) → y≤x , x≰y ∘ reflx→fromeq _≤_ rfl ∘ PT.map sym
  }) (total x y)

≮⇒≥ : Discrete A → Reflexive _≤_ → Total _≤_ →
      ∀ {x y} → ¬ ⟨ x < y ⟩ → ⟨ y ≤ x ⟩
≮⇒≥ _≟_ ≤-refl _≤?_ {x} {y} x≮y with x ≟ y
... | yes x≈y = reflx→fromeq _≤_ ≤-refl ∣ sym x≈y ∣
... | no x≢y = PT.rec ((y ≤ x) .snd) (λ {
        (inl y≤x) → y≤x
      ; (inr x≤y) → elim (x≮y (x≤y , x≢y ∘ PT.rec (Discrete→isSet _≟_ _ _) id))
      }) (y ≤? x)
------------------------------------------------------------------------
-- Relational properties

<-toNotEq : ToNotEq _<_
<-toNotEq (_ , x≢y) x≡y = x≢y x≡y

<-irrefl : Irreflexive _<_
<-irrefl = tonoteq→irrefl _<_ <-toNotEq

<-transitive : IsPartialOrder _≤_ → Transitive _<_
<-transitive po (x≤y , x≢y) (y≤z , y≉z) =
  (transitive x≤y y≤z , x≢y ∘ antisym x≤y ∘ transitive y≤z ∘ fromEq ∘ PT.map sym)
  where open IsPartialOrder po

<-≤-trans : Transitive _≤_ → Antisymmetric _≤_ →
           Trans _<_ _≤_ _<_
<-≤-trans transitive antisym (x≤y , x≢y) y≤z =
  transitive x≤y y≤z , (λ x≡z → x≢y (antisym x≤y (Respectsʳ≡ₚ _≤_ (PT.map sym x≡z) y≤z)))

≤-<-trans : Transitive _≤_ → Antisymmetric _≤_ →
           Trans _≤_ _<_ _<_
≤-<-trans trans antisym x≤y (y≤z , y≢z) =
  trans x≤y y≤z , (λ x≡z → y≢z (antisym y≤z (Respectsˡ≡ₚ _≤_ x≡z x≤y)))

<-asym : Antisymmetric _≤_ → Asymmetric _<_
<-asym antisym (x≤y , x≢y) (y≤x , _) = x≢y (antisym x≤y y≤x)
{-
<-trichotomous : Discrete A → Antisymmetric _≤_ → Total _≤_ → Trichotomous _<_
<-trichotomous _≟_ antisym total x y with x ≟ y
... | yes x≡y = tri≡ (λ x<y → ?) x≡y (λ y<x → <-toNotEq y<x (PT.map sym x≡y))
... | no  x≢y with total x y
...   | inl x≤y = tri< (x≤y , x≢y) x≢y (x≢y ∘ antisym x≤y ∘ proj₁)
...   | inr y≤x = tri> (x≢y ∘ flip antisym y≤x ∘ proj₁) x≢y (y≤x , x≢y ∘ sym)
-}
<-decidable : Discrete A → Decidable _≤_ → Decidable _<_
<-decidable _≟_ _≤?_ x y with x ≤? y
... | no ¬p = no (¬p ∘ fst)
... | yes p with x ≟ y
...   | yes q = no (λ x<y → snd x<y ∣ q ∣)
...   | no ¬q = yes (p , ¬q ∘ PT.rec (Discrete→isSet _≟_ _ _) id)

------------------------------------------------------------------------
-- Structures
{-
isStrictPartialOrder : IsPartialOrder _≤_ → IsStrictPartialOrder _<_
isStrictPartialOrder po = record
  { irrefl     = <-irrefl
  ; transitive = <-transitive po
  } where open IsPartialOrder po

isStrictTotalOrder₁ : Discrete A → IsTotalOrder _≤_ →
                        IsStrictTotalOrder _<_
isStrictTotalOrder₁ ≟ tot = record
  { transitive = <-transitive isPartialOrder
  ; compare    = <-trichotomous ≟ antisym total
  } where open IsTotalOrder tot

isStrictTotalOrder₂ : IsDecTotalOrder _≤_ → IsStrictTotalOrder _<_
isStrictTotalOrder₂ dtot = isStrictTotalOrder₁ _≟_ isTotalOrder
  where open IsDecTotalOrder dtot
-}
