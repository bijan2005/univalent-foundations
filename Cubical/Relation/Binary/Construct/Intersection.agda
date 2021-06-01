{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Construct.Intersection where

open import Cubical.Core.Everything
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic using (_⊓_)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr; rec)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary using (yes; no; Dec)

------------------------------------------------------------------------
-- Definition

_∩_ : ∀ {a b ℓ₁ ℓ₂} {A : Type a} {B : Type b} →
      REL A B ℓ₁ → REL A B ℓ₂ → REL A B (ℓ-max ℓ₁ ℓ₂)
L ∩ R = λ i j → L i j ⊓ R i j

------------------------------------------------------------------------
-- Properties

module _ {a ℓ₁ ℓ₂} {A : Type a} (L : Rel A ℓ₁) (R : Rel A ℓ₂) where

  reflexive : Reflexive L → Reflexive R → Reflexive (L ∩ R)
  reflexive L-refl R-refl = L-refl , R-refl

  symmetric : Symmetric L → Symmetric R → Symmetric (L ∩ R)
  symmetric L-sym R-sym = map-× L-sym R-sym

  transitive : Transitive L → Transitive R → Transitive (L ∩ R)
  transitive L-trans R-trans (xLy , xRy) (yLz , yRz) = L-trans xLy yLz , R-trans xRy yRz

  respects : ∀ {p} (P : A → hProp p) →
             P Respects L ⊎ P Respects R → P Respects (L ∩ R)
  respects P resp (Lxy , Rxy) = rec (λ x → x Lxy) (λ x → x Rxy) resp

  min : ∀ {⊤} → Minimum L ⊤ → Minimum R ⊤ → Minimum (L ∩ R) ⊤
  min L-min R-min x = L-min x , R-min x

  max : ∀ {⊥} → Maximum L ⊥ → Maximum R ⊥ → Maximum (L ∩ R) ⊥
  max L-max R-max x = L-max x , R-max x

  toNotEq : ToNotEq L ⊎ ToNotEq R → ToNotEq (L ∩ R)
  toNotEq tonoteq (Lxy , Rxy) x≡y = rec (λ x → x Lxy x≡y) (λ y → y Rxy x≡y) tonoteq

  irreflexive : Irreflexive L ⊎ Irreflexive R → Irreflexive (L ∩ R)
  irreflexive irrefl (xLx , xRx) = rec (λ x → x xLx) (λ y → y xRx) irrefl

  antisymmetric : Antisymmetric L ⊎ Antisymmetric R → Antisymmetric (L ∩ R)
  antisymmetric (inl L-antisym) (Lxy , _) (Lyx , _) = L-antisym Lxy Lyx
  antisymmetric (inr R-antisym) (_ , Rxy) (_ , Ryx) = R-antisym Rxy Ryx

module _ {a b ℓ₁ ℓ₂ ℓ₃} {A : Type a} {B : Type b}
         (≈ : REL A B ℓ₁) {L : REL A B ℓ₂} {R : REL A B ℓ₃} where

  implies : (≈ ⇒ L) → (≈ ⇒ R) → ≈ ⇒ (L ∩ R)
  implies ≈⇒L ≈⇒R ≈ = ≈⇒L ≈ , ≈⇒R ≈

module _ {a ℓ₁ ℓ₂ ℓ₃} {A : Type a}
         (≈ : Rel A ℓ₁) (L : Rel A ℓ₂) (R : Rel A ℓ₃) where

  respectsˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∩ R) Respectsˡ ≈
  respectsˡ L-resp R-resp x≈y = map-× (L-resp x≈y) (R-resp x≈y)

  respectsʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∩ R) Respectsʳ ≈
  respectsʳ L-resp R-resp x≈y = map-× (L-resp x≈y) (R-resp x≈y)

  respects₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∩ R) Respects₂ ≈
  respects₂ (Lʳ , Lˡ) (Rʳ , Rˡ) = respectsʳ Lʳ Rʳ , respectsˡ Lˡ Rˡ

module _ {a b ℓ₁ ℓ₂} {A : Type a} {B : Type b} (L : REL A B ℓ₁) (R : REL A B ℓ₂) where

  decidable : Decidable L → Decidable R → Decidable (L ∩ R)
  decidable L? R? x y = ×-dec (L? x y) (R? x y)
    where
      ×-dec : ∀ {a b} {A : Type a} {B : Type b} → Dec A → Dec B → Dec (A × B)
      ×-dec (yes a) (yes b) = yes (a , b)
      ×-dec _       (no ¬b) = no (¬b ∘ snd)
      ×-dec (no ¬a) _       = no (¬a ∘ fst)
------------------------------------------------------------------------
-- Structures

module _ {a ℓ₁ ℓ₂} {A : Type a} {L : Rel A ℓ₁} {R : Rel A ℓ₂} where

  isPartialEquivalence : IsPartialEquivalence L → IsPartialEquivalence R → IsPartialEquivalence (L ∩ R)
  isPartialEquivalence eqₗ eqᵣ = record
    { symmetric  = symmetric  L R Eqₗ.symmetric  Eqᵣ.symmetric
    ; transitive = transitive L R Eqₗ.transitive Eqᵣ.transitive
    }
    where module Eqₗ = IsPartialEquivalence eqₗ; module Eqᵣ = IsPartialEquivalence eqᵣ

  isEquivalence : IsEquivalence L → IsEquivalence R → IsEquivalence (L ∩ R)
  isEquivalence eqₗ eqᵣ = record
    { isPartialEquivalence = isPartialEquivalence Eqₗ.isPartialEquivalence Eqᵣ.isPartialEquivalence
    ; reflexive            = reflexive L R Eqₗ.reflexive Eqᵣ.reflexive
    }
    where module Eqₗ = IsEquivalence eqₗ; module Eqᵣ = IsEquivalence eqᵣ

  isDecEquivalence : IsDecEquivalence L → IsDecEquivalence R → IsDecEquivalence (L ∩ R)
  isDecEquivalence eqₗ eqᵣ = record
    { isEquivalence = isEquivalence Eqₗ.isEquivalence Eqᵣ.isEquivalence
    ; _≟_           = decidable L R Eqₗ._≟_ Eqᵣ._≟_
    }
    where module Eqₗ = IsDecEquivalence eqₗ; module Eqᵣ = IsDecEquivalence eqᵣ

  isPreorder : IsPreorder L → IsPreorder R → IsPreorder (L ∩ R)
  isPreorder Oₗ Oᵣ = record
    { reflexive  = reflexive L R Oₗ.reflexive Oᵣ.reflexive
    ; transitive = transitive L R Oₗ.transitive Oᵣ.transitive
    }
    where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPreorder Oᵣ

  isPartialOrderˡ : IsPartialOrder L → IsPreorder R → IsPartialOrder (L ∩ R)
  isPartialOrderˡ Oₗ Oᵣ = record
    { isPreorder = isPreorder Oₗ.isPreorder Oᵣ
    ; antisym    = antisymmetric L R (inl Oₗ.antisym)
    }
    where module Oₗ = IsPartialOrder Oₗ; module Oᵣ = IsPreorder Oᵣ

  isPartialOrderʳ : IsPreorder L → IsPartialOrder R → IsPartialOrder (L ∩ R)
  isPartialOrderʳ Oₗ Oᵣ = record
    { isPreorder = isPreorder Oₗ Oᵣ.isPreorder
    ; antisym    = antisymmetric L R (inr Oᵣ.antisym)
    }
    where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPartialOrder Oᵣ

  isStrictPartialOrderˡ : IsStrictPartialOrder L → Transitive R → IsStrictPartialOrder (L ∩ R)
  isStrictPartialOrderˡ Oₗ transitiveᵣ = record
    { irrefl     = irreflexive L R (inl Oₗ.irrefl)
    ; transitive = transitive L R Oₗ.transitive transitiveᵣ
    }
    where module Oₗ = IsStrictPartialOrder Oₗ

  isStrictPartialOrderʳ : Transitive L → IsStrictPartialOrder R → IsStrictPartialOrder (L ∩ R)
  isStrictPartialOrderʳ transitiveₗ Oᵣ = record
    { irrefl     = irreflexive L R (inr Oᵣ.irrefl)
    ; transitive = transitive L R transitiveₗ Oᵣ.transitive
    }
    where module Oᵣ = IsStrictPartialOrder Oᵣ
