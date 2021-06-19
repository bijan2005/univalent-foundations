{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.MorphismProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_; id)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Semigroup.Morphism

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Pointed

open import Cubical.Algebra.Magma.Properties using (isPropIsMagma)

open import Cubical.Relation.Binary.Reasoning.Equality

open Iso

private
  variable
    ℓ ℓ′ ℓ′′ : Level

isPropIsSemigroupHom : ∀ (S : Semigroup ℓ) (T : Semigroup ℓ′) f → isProp (IsSemigroupHom S T f)
isPropIsSemigroupHom S T f = isPropHomomorphic₂ (Semigroup.is-set T) f (Semigroup._•_ S) (Semigroup._•_ T)

isSetSemigroupHom : {S : Semigroup ℓ} {T : Semigroup ℓ′} → isSet (SemigroupHom S T)
isSetSemigroupHom {S = S} {T = T} = isOfHLevelRespectEquiv 2 equiv (isSetΣ (isSetΠ λ _ → is-set T) (λ f → isProp→isSet (isPropIsSemigroupHom S T f)))
  where
    open Semigroup
    equiv : (Σ[ g ∈ (⟨ S ⟩ → ⟨ T ⟩) ] IsSemigroupHom S T g) ≃ SemigroupHom S T
    equiv = isoToEquiv (iso (λ (g , m) → semigrouphom g m) (λ (semigrouphom g m) → g , m) (λ _ → refl) λ _ → refl)

isSemigroupHomComp : {R : Semigroup ℓ} {S : Semigroup ℓ′} {T : Semigroup ℓ′′} {f : ⟨ R ⟩ → ⟨ S ⟩} {g : ⟨ S ⟩ → ⟨ T ⟩} →
                  IsSemigroupHom R S f → IsSemigroupHom S T g → IsSemigroupHom R T (g ∘ f)
isSemigroupHomComp {g = g} fHom gHom _ _ = cong g (fHom _ _) ∙ gHom _ _

private
  isSemigroupHomComp′ : {R : Semigroup ℓ} {S : Semigroup ℓ′} {T : Semigroup ℓ′′} (f : SemigroupHom R S) (g : SemigroupHom S T) →
                    IsSemigroupHom R T (SemigroupHom.fun g ∘ SemigroupHom.fun f)
  isSemigroupHomComp′ (semigrouphom f fHom) (semigrouphom g gHom) _ _ = cong g (fHom _ _) ∙ gHom _ _

compSemigroupHom : {R : Semigroup ℓ} {S : Semigroup ℓ′} {T : Semigroup ℓ′′} →
                SemigroupHom R S → SemigroupHom S T → SemigroupHom R T
compSemigroupHom {R = R} {S} {T} f g =
  semigrouphom _ (isSemigroupHomComp′ f g)

compSemigroupEquiv : {R : Semigroup ℓ} {S : Semigroup ℓ′} {T : Semigroup ℓ′′} →
                  SemigroupEquiv R S → SemigroupEquiv S T → SemigroupEquiv R T
compSemigroupEquiv {R = R} {S} {T} f g = semigroupequiv (compEquiv f.eq g.eq) (isSemigroupHomComp′ f.hom g.hom)
  where
    module f = SemigroupEquiv f
    module g = SemigroupEquiv g

isSemigroupHomId : (S : Semigroup ℓ) → IsSemigroupHom S S id
isSemigroupHomId S _ _ = refl

idSemigroupHom : (S : Semigroup ℓ) → SemigroupHom S S
idSemigroupHom S = record
  { fun   = id
  ; isHom = isSemigroupHomId S
  }

idSemigroupEquiv : (S : Semigroup ℓ) → SemigroupEquiv S S
idSemigroupEquiv S = record
  { eq    = idEquiv ⟨ S ⟩
  ; isHom = isSemigroupHomId S
  }

-- Isomorphism inversion
isSemigroupHomInv : {S : Semigroup ℓ} {T : Semigroup ℓ′} → (eqv : SemigroupEquiv S T) → IsSemigroupHom T S (invEq (SemigroupEquiv.eq eqv))
isSemigroupHomInv {S = S} {T} (semigroupequiv eq isHom) x y = isInj-f _ _ (
  f (f⁻¹ (x •ᵀ y))       ≡⟨ retEq eq _ ⟩
  x •ᵀ y                 ≡˘⟨ cong₂ _•ᵀ_ (retEq eq x) (retEq eq y) ⟩
  f (f⁻¹ x) •ᵀ f (f⁻¹ y) ≡˘⟨ isHom (f⁻¹ x) (f⁻¹ y) ⟩
  f (f⁻¹ x • f⁻¹ y)      ∎)
  where
    _•_ = Semigroup._•_ S -- superscript S isn't available for some reason
    _•ᵀ_ = Semigroup._•_ T
    f = equivFun eq
    f⁻¹ = invEq eq
    isInj-f : (x y : ⟨ S ⟩) → f x ≡ f y → x ≡ y
    isInj-f x y = invEq (_ , isEquiv→isEmbedding (eq .snd) x y)

invSemigroupHom : {S : Semigroup ℓ} {T : Semigroup ℓ′} → SemigroupEquiv S T → SemigroupHom T S
invSemigroupHom eq = record { isHom = isSemigroupHomInv eq }

invSemigroupEquiv : {S : Semigroup ℓ} {T : Semigroup ℓ′} → SemigroupEquiv S T → SemigroupEquiv T S
invSemigroupEquiv eq = record
  { eq    = invEquiv (SemigroupEquiv.eq eq)
  ; isHom = isSemigroupHomInv eq
  }

semigroupHomEq : {S : Semigroup ℓ} {T : Semigroup ℓ′} {f g : SemigroupHom S T} → (SemigroupHom.fun f ≡ SemigroupHom.fun g) → f ≡ g
semigroupHomEq {S = S} {T} {semigrouphom f fm} {semigrouphom g gm} p i = semigrouphom (p i) (p-hom i) where
  p-hom : PathP (λ i → IsSemigroupHom S T (p i)) fm gm
  p-hom = toPathP (isPropIsSemigroupHom S T _ _ _)

semigroupEquivEq : {S : Semigroup ℓ} {T : Semigroup ℓ′} {f g : SemigroupEquiv S T} → (SemigroupEquiv.eq f ≡ SemigroupEquiv.eq g) → f ≡ g
semigroupEquivEq {S = S} {T} {semigroupequiv f fm} {semigroupequiv g gm} p i = semigroupequiv (p i) (p-hom i) where
  p-hom : PathP (λ i → IsSemigroupHom S T (p i .fst)) fm gm
  p-hom = toPathP (isPropIsSemigroupHom S T _ _ _)

module SemigroupΣTheory {ℓ} where

  RawSemigroupStructure : Type ℓ → Type ℓ
  RawSemigroupStructure X = X → X → X

  RawSemigroupEquivStr = AutoEquivStr RawSemigroupStructure

  rawSemigroupUnivalentStr : UnivalentStr _ RawSemigroupEquivStr
  rawSemigroupUnivalentStr = autoUnivalentStr RawSemigroupStructure

  SemigroupAxioms : (A : Type ℓ) → RawSemigroupStructure A → Type ℓ
  SemigroupAxioms A _•_ = IsMagma A _•_ × Associative _•_

  SemigroupStructure : Type ℓ → Type ℓ
  SemigroupStructure = AxiomsStructure RawSemigroupStructure SemigroupAxioms

  SemigroupΣ : Type (ℓ-suc ℓ)
  SemigroupΣ = TypeWithStr ℓ SemigroupStructure

  isPropSemigroupAxioms : (A : Type ℓ) (_•_ : RawSemigroupStructure A) →
                          isProp (SemigroupAxioms A _•_)
  isPropSemigroupAxioms A _•_ = isPropΣ isPropIsMagma λ isMagmaA → isPropAssociative (IsMagma.is-set isMagmaA) _•_

  SemigroupEquivStr : StrEquiv SemigroupStructure ℓ
  SemigroupEquivStr = AxiomsEquivStr RawSemigroupEquivStr SemigroupAxioms

  SemigroupAxiomsIsoIsSemigroup : {A : Type ℓ} {_•_ : RawSemigroupStructure A} →
                                  Iso (SemigroupAxioms A _•_) (IsSemigroup A _•_)
  fun SemigroupAxiomsIsoIsSemigroup (x , y)           = issemigroup x y
  inv SemigroupAxiomsIsoIsSemigroup (issemigroup x y) = (x , y)
  rightInv SemigroupAxiomsIsoIsSemigroup _            = refl
  leftInv SemigroupAxiomsIsoIsSemigroup _             = refl

  SemigroupAxioms≡IsSemigroup : {A : Type ℓ} {_•_ : RawSemigroupStructure A} →
                                SemigroupAxioms _ _•_ ≡ IsSemigroup A _•_
  SemigroupAxioms≡IsSemigroup = isoToPath SemigroupAxiomsIsoIsSemigroup

  Semigroup→SemigroupΣ : Semigroup ℓ → SemigroupΣ
  Semigroup→SemigroupΣ (mksemigroup A _•_ isSemigroupA) =
    A , _•_ , SemigroupAxiomsIsoIsSemigroup .inv isSemigroupA

  SemigroupΣ→Semigroup : SemigroupΣ → Semigroup ℓ
  SemigroupΣ→Semigroup (A , _•_ , isSemigroupA) =
    mksemigroup A _•_ (SemigroupAxiomsIsoIsSemigroup .fun isSemigroupA)

  SemigroupIsoSemigroupΣ : Iso (Semigroup ℓ) SemigroupΣ
  SemigroupIsoSemigroupΣ =
    iso Semigroup→SemigroupΣ SemigroupΣ→Semigroup (λ _ → refl) (λ _ → refl)

  semigroupUnivalentStr : UnivalentStr SemigroupStructure SemigroupEquivStr
  semigroupUnivalentStr = axiomsUnivalentStr _ isPropSemigroupAxioms rawSemigroupUnivalentStr

  SemigroupΣPath : (S T : SemigroupΣ) → (S ≃[ SemigroupEquivStr ] T) ≃ (S ≡ T)
  SemigroupΣPath = SIP semigroupUnivalentStr

  SemigroupEquivΣ : (S T : Semigroup ℓ) → Type ℓ
  SemigroupEquivΣ S T = Semigroup→SemigroupΣ S ≃[ SemigroupEquivStr ] Semigroup→SemigroupΣ T

  SemigroupIsoΣPath : {S T : Semigroup ℓ} → Iso (SemigroupEquiv S T) (SemigroupEquivΣ S T)
  fun SemigroupIsoΣPath (semigroupequiv e h) = (e , h)
  inv SemigroupIsoΣPath (e , h)            = semigroupequiv e h
  rightInv SemigroupIsoΣPath _             = refl
  leftInv SemigroupIsoΣPath _              = refl

  SemigroupPath : (S T : Semigroup ℓ) → (SemigroupEquiv S T) ≃ (S ≡ T)
  SemigroupPath S T =
    SemigroupEquiv S T                                ≃⟨ isoToEquiv SemigroupIsoΣPath ⟩
    SemigroupEquivΣ S T                               ≃⟨ SemigroupΣPath _ _ ⟩
    Semigroup→SemigroupΣ S ≡ Semigroup→SemigroupΣ T   ≃⟨ isoToEquiv (invIso (congIso SemigroupIsoSemigroupΣ)) ⟩
    S ≡ T                                             ■

  RawSemigroupΣ : Type (ℓ-suc ℓ)
  RawSemigroupΣ = TypeWithStr ℓ RawSemigroupStructure

  Semigroup→RawSemigroupΣ : Semigroup ℓ → RawSemigroupΣ
  Semigroup→RawSemigroupΣ S = (⟨ S ⟩ , Semigroup._•_ S)

  InducedSemigroup : (S : Semigroup ℓ) (T : RawSemigroupΣ) (e : ⟨ S ⟩ ≃ ⟨ T ⟩) →
                      RawSemigroupEquivStr (Semigroup→RawSemigroupΣ S) T e → Semigroup ℓ
  InducedSemigroup S T e r =
    SemigroupΣ→Semigroup (inducedStructure rawSemigroupUnivalentStr (Semigroup→SemigroupΣ S) T (e , r))

  InducedSemigroupPath : (S : Semigroup ℓ) (T : RawSemigroupΣ) (e : ⟨ S ⟩ ≃ ⟨ T ⟩)
                          (E : RawSemigroupEquivStr (Semigroup→RawSemigroupΣ S) T e) →
                          S ≡ InducedSemigroup S T e E
  InducedSemigroupPath S T e E =
    SemigroupPath S (InducedSemigroup S T e E) .fst (semigroupequiv e E)

-- We now extract the important results from the above module

open SemigroupΣTheory public using (InducedSemigroup; InducedSemigroupPath)

SemigroupPath : {S T : Semigroup ℓ} → (SemigroupEquiv S T) ≃ (S ≡ T)
SemigroupPath = SemigroupΣTheory.SemigroupPath _ _

isPropIsSemigroup : {A : Type ℓ} {_•_ : Op₂ A} → isProp (IsSemigroup A _•_)
isPropIsSemigroup =
  subst isProp SemigroupΣTheory.SemigroupAxioms≡IsSemigroup
        (SemigroupΣTheory.isPropSemigroupAxioms _ _)

open Semigroup

uaSemigroup : {S T : Semigroup ℓ} → SemigroupEquiv S T → S ≡ T
uaSemigroup = equivFun SemigroupPath

carac-uaSemigroup : {S T : Semigroup ℓ} (f : SemigroupEquiv S T) → cong Carrier (uaSemigroup f) ≡ ua (SemigroupEquiv.eq f)
carac-uaSemigroup (semigroupequiv f m) =
  (refl ∙∙ ua f ∙∙ refl)
    ≡˘⟨ rUnit (ua f) ⟩
  ua f ∎

Semigroup≡ : (S T : Semigroup ℓ) → (
  Σ[ p ∈ ⟨ S ⟩ ≡ ⟨ T ⟩ ]
  Σ[ q ∈ PathP (λ i → p i → p i → p i) (_•_ S) (_•_ T) ]
  PathP (λ i → IsSemigroup (p i) (q i)) (isSemigroup S) (isSemigroup T))
  ≃ (S ≡ T)
Semigroup≡ S T = isoToEquiv (iso
  (λ (p , q , r) i → mksemigroup (p i) (q i) (r i))
  (λ p → cong Carrier p , cong _•_ p , cong isSemigroup p)
  (λ _ → refl) (λ _ → refl))

caracSemigroup≡ : {S T : Semigroup ℓ} (p q : S ≡ T) → cong Carrier p ≡ cong Carrier q → p ≡ q
caracSemigroup≡ {S = S} {T} p q t = cong (fst (Semigroup≡ S T)) (Σ≡Prop (λ _ →
    isPropΣ
    (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set T) _ _) λ _ →
    isOfHLevelPathP 1 isPropIsSemigroup _ _)
  t)

uaSemigroupId : (S : Semigroup ℓ) → uaSemigroup (idSemigroupEquiv S) ≡ refl
uaSemigroupId S = caracSemigroup≡ _ _ (carac-uaSemigroup (idSemigroupEquiv S) ∙ uaIdEquiv)

uaCompSemigroupEquiv : {R S T : Semigroup ℓ} (f : SemigroupEquiv R S) (g : SemigroupEquiv S T) → uaSemigroup (compSemigroupEquiv f g) ≡ uaSemigroup f ∙ uaSemigroup g
uaCompSemigroupEquiv f g = caracSemigroup≡ _ _ (
  cong Carrier (uaSemigroup (compSemigroupEquiv f g))
    ≡⟨ carac-uaSemigroup (compSemigroupEquiv f g) ⟩
  ua (eq (compSemigroupEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  ua (eq f) ∙ ua (eq g)
    ≡˘⟨ cong (_∙ ua (eq g)) (carac-uaSemigroup f) ⟩
  cong Carrier (uaSemigroup f) ∙ ua (eq g)
    ≡˘⟨ cong (cong Carrier (uaSemigroup f) ∙_) (carac-uaSemigroup g) ⟩
  cong Carrier (uaSemigroup f) ∙ cong Carrier (uaSemigroup g)
    ≡˘⟨ cong-∙ Carrier (uaSemigroup f) (uaSemigroup g) ⟩
  cong Carrier (uaSemigroup f ∙ uaSemigroup g) ∎)
  where open SemigroupEquiv
