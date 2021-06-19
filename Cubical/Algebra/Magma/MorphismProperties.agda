{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma.MorphismProperties where

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
open import Cubical.Data.Prod using (isPropProd)

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Magma.Morphism

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Record

open import Cubical.Relation.Binary.Reasoning.Equality

open Iso

private
  variable
    ℓ ℓ′ ℓ′′ : Level

isPropIsMagmaHom : ∀ (M : Magma ℓ) (N : Magma ℓ′) f → isProp (IsMagmaHom M N f)
isPropIsMagmaHom M N f = isPropHomomorphic₂ (Magma.is-set N) f (Magma._•_ M) (Magma._•_ N)

isSetMagmaHom : {M : Magma ℓ} {N : Magma ℓ′} → isSet (MagmaHom M N)
isSetMagmaHom {M = M} {N} = isOfHLevelRespectEquiv 2 equiv (isSetΣ (isSetΠ λ _ → is-set N) (λ f → isProp→isSet (isPropIsMagmaHom M N f)))
  where
    open Magma
    equiv : (Σ[ g ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsMagmaHom M N g) ≃ MagmaHom M N
    equiv = isoToEquiv (iso (λ (g , m) → magmahom g m) (λ (magmahom g m) → g , m) (λ _ → refl) λ _ → refl)

isMagmaHomComp : {L : Magma ℓ} {M : Magma ℓ′} {N : Magma ℓ′′} {f : ⟨ L ⟩ → ⟨ M ⟩} {g : ⟨ M ⟩ → ⟨ N ⟩} →
                  IsMagmaHom L M f → IsMagmaHom M N g → IsMagmaHom L N (g ∘ f)
isMagmaHomComp {g = g} fHom gHom _ _ = cong g (fHom _ _) ∙ gHom _ _

private
  isMagmaHomComp′ : {L : Magma ℓ} {M : Magma ℓ′} {N : Magma ℓ′′} (f : MagmaHom L M) (g : MagmaHom M N) →
                    IsMagmaHom L N (MagmaHom.fun g ∘ MagmaHom.fun f)
  isMagmaHomComp′ (magmahom f fHom) (magmahom g gHom) _ _ = cong g (fHom _ _) ∙ gHom _ _

compMagmaHom : {L : Magma ℓ} {M : Magma ℓ′} {N : Magma ℓ′′} →
                MagmaHom L M → MagmaHom M N → MagmaHom L N
compMagmaHom {L = L} {M} {N} f g =
  magmahom _ (isMagmaHomComp′ f g)

compMagmaEquiv : {L : Magma ℓ} {M : Magma ℓ′} {N : Magma ℓ′′} →
                  MagmaEquiv L M → MagmaEquiv M N → MagmaEquiv L N
compMagmaEquiv {L = L} {M} {N} f g = magmaequiv (compEquiv f.eq g.eq) (isMagmaHomComp′ f.hom g.hom)
  where
    module f = MagmaEquiv f
    module g = MagmaEquiv g

isMagmaHomId : (M : Magma ℓ) → IsMagmaHom M M id
isMagmaHomId M _ _ = refl

idMagmaHom : (M : Magma ℓ) → MagmaHom M M
idMagmaHom M = record
  { fun   = id
  ; isHom = isMagmaHomId M
  }

idMagmaEquiv : (M : Magma ℓ) → MagmaEquiv M M
idMagmaEquiv M = record
  { eq    = idEquiv ⟨ M ⟩
  ; isHom = isMagmaHomId M
  }

-- Isomorphism inversion
isMagmaHomInv : {M : Magma ℓ} {N : Magma ℓ′} → (eqv : MagmaEquiv M N) → IsMagmaHom N M (invEq (MagmaEquiv.eq eqv))
isMagmaHomInv {M = M} {N} (magmaequiv eq isHom) x y = isInj-f _ _ (
  f (f⁻¹ (x •ᴺ y))       ≡⟨ retEq eq _ ⟩
  x •ᴺ y                 ≡˘⟨ cong₂ _•ᴺ_ (retEq eq x) (retEq eq y) ⟩
  f (f⁻¹ x) •ᴺ f (f⁻¹ y) ≡˘⟨ isHom (f⁻¹ x) (f⁻¹ y) ⟩
  f (f⁻¹ x •ᴹ f⁻¹ y)     ∎)
  where
    _•ᴹ_ = Magma._•_ M
    _•ᴺ_ = Magma._•_ N
    f = equivFun eq
    f⁻¹ = invEq eq
    isInj-f : (x y : ⟨ M ⟩) → f x ≡ f y → x ≡ y
    isInj-f x y = invEq (_ , isEquiv→isEmbedding (eq .snd) x y)

invMagmaHom : {M : Magma ℓ} {N : Magma ℓ′} → MagmaEquiv M N → MagmaHom N M
invMagmaHom eq = record { isHom = isMagmaHomInv eq }

invMagmaEquiv : {M : Magma ℓ} {N : Magma ℓ′} → MagmaEquiv M N → MagmaEquiv N M
invMagmaEquiv eq = record
  { eq    = invEquiv (MagmaEquiv.eq eq)
  ; isHom = isMagmaHomInv eq
  }

magmaHomEq : {M : Magma ℓ} {N : Magma ℓ′} {f g : MagmaHom M N} → (MagmaHom.fun f ≡ MagmaHom.fun g) → f ≡ g
magmaHomEq {M = M} {N} {magmahom f fm} {magmahom g gm} p i = magmahom (p i) (p-hom i)
  where
    p-hom : PathP (λ i → IsMagmaHom M N (p i)) fm gm
    p-hom = toPathP (isPropIsMagmaHom M N _ _ _)

magmaEquivEq : {M : Magma ℓ} {N : Magma ℓ′} {f g : MagmaEquiv M N} → (MagmaEquiv.eq f ≡ MagmaEquiv.eq g) → f ≡ g
magmaEquivEq {M = M} {N} {magmaequiv f fm} {magmaequiv g gm} p i = magmaequiv (p i) (p-hom i)
  where
    p-hom : PathP (λ i → IsMagmaHom M N (p i .fst)) fm gm
    p-hom = toPathP (isPropIsMagmaHom M N _ _ _)

module MagmaΣTheory {ℓ} where

  RawMagmaStructure : Type ℓ → Type ℓ
  RawMagmaStructure A = A → A → A

  RawMagmaEquivStr = AutoEquivStr RawMagmaStructure

  rawMagmaUnivalentStr : UnivalentStr _ RawMagmaEquivStr
  rawMagmaUnivalentStr = autoUnivalentStr RawMagmaStructure

  MagmaAxioms : (A : Type ℓ) → RawMagmaStructure A → Type ℓ
  MagmaAxioms A _•_ = isSet A

  MagmaStructure : Type ℓ → Type ℓ
  MagmaStructure = AxiomsStructure RawMagmaStructure MagmaAxioms

  MagmaΣ : Type (ℓ-suc ℓ)
  MagmaΣ = TypeWithStr ℓ MagmaStructure

  isPropMagmaAxioms : (A : Type ℓ) (_•_ : RawMagmaStructure A)
                      → isProp (MagmaAxioms A _•_)
  isPropMagmaAxioms _ _ = isPropIsSet

  MagmaEquivStr : StrEquiv MagmaStructure ℓ
  MagmaEquivStr = AxiomsEquivStr RawMagmaEquivStr MagmaAxioms

  MagmaAxiomsIsoIsMagma : {A : Type ℓ} (_•_ : RawMagmaStructure A)
                              → Iso (MagmaAxioms A _•_) (IsMagma A _•_)
  fun (MagmaAxiomsIsoIsMagma s) x           = ismagma x
  inv (MagmaAxiomsIsoIsMagma s) (ismagma x) = x
  rightInv (MagmaAxiomsIsoIsMagma s) _      = refl
  leftInv (MagmaAxiomsIsoIsMagma s) _       = refl

  MagmaAxioms≡IsMagma : {A : Type ℓ} (_•_ : RawMagmaStructure A)
                              → MagmaAxioms A _•_ ≡ IsMagma A _•_
  MagmaAxioms≡IsMagma s = isoToPath (MagmaAxiomsIsoIsMagma s)

  Magma→MagmaΣ : Magma ℓ → MagmaΣ
  Magma→MagmaΣ (mkmagma A _•_ isMagma) =
    A , _•_ , MagmaAxiomsIsoIsMagma _ .inv isMagma

  MagmaΣ→Magma : MagmaΣ → Magma ℓ
  MagmaΣ→Magma (A , _•_ , isMagma•) =
    mkmagma A _•_ (MagmaAxiomsIsoIsMagma _ .fun isMagma•)

  MagmaIsoMagmaΣ : Iso (Magma ℓ) MagmaΣ
  MagmaIsoMagmaΣ =
    iso Magma→MagmaΣ MagmaΣ→Magma (λ _ → refl) (λ _ → refl)

  magmaUnivalentStr : UnivalentStr MagmaStructure MagmaEquivStr
  magmaUnivalentStr = axiomsUnivalentStr _ isPropMagmaAxioms rawMagmaUnivalentStr

  MagmaΣPath : (M N : MagmaΣ) → (M ≃[ MagmaEquivStr ] N) ≃ (M ≡ N)
  MagmaΣPath = SIP magmaUnivalentStr

  MagmaEquivΣ : (M N : Magma ℓ) → Type ℓ
  MagmaEquivΣ M N = Magma→MagmaΣ M ≃[ MagmaEquivStr ] Magma→MagmaΣ N

  MagmaIsoΣPath : {M N : Magma ℓ} → Iso (MagmaEquiv M N) (MagmaEquivΣ M N)
  fun MagmaIsoΣPath (magmaequiv e h)   = (e , h)
  inv MagmaIsoΣPath (e , h)            = magmaequiv e h
  rightInv MagmaIsoΣPath _             = refl
  leftInv MagmaIsoΣPath _              = refl

  MagmaPath : (M N : Magma ℓ) → (MagmaEquiv M N) ≃ (M ≡ N)
  MagmaPath M N =
    MagmaEquiv M N                    ≃⟨ isoToEquiv MagmaIsoΣPath ⟩
    MagmaEquivΣ M N                   ≃⟨ MagmaΣPath _ _ ⟩
    Magma→MagmaΣ M ≡ Magma→MagmaΣ N   ≃⟨ isoToEquiv (invIso (congIso MagmaIsoMagmaΣ)) ⟩
    M ≡ N                             ■

  RawMagmaΣ : Type (ℓ-suc ℓ)
  RawMagmaΣ = TypeWithStr ℓ RawMagmaStructure

  Magma→RawMagmaΣ : Magma ℓ → RawMagmaΣ
  Magma→RawMagmaΣ M = (⟨ M ⟩ , Magma._•_ M)

  InducedMagma : (M : Magma ℓ) (N : RawMagmaΣ) (e : ⟨ M ⟩ ≃ ⟨ N ⟩)
                 → RawMagmaEquivStr (Magma→RawMagmaΣ M) N e → Magma ℓ
  InducedMagma M N e r =
    MagmaΣ→Magma (inducedStructure rawMagmaUnivalentStr (Magma→MagmaΣ M) N (e , r))

  InducedMagmaPath : (M : Magma ℓ) (N : RawMagmaΣ) (e : ⟨ M ⟩ ≃ ⟨ N ⟩)
                      (E : RawMagmaEquivStr (Magma→RawMagmaΣ M) N e)
                    → M ≡ InducedMagma M N e E
  InducedMagmaPath M N e E =
    MagmaPath M (InducedMagma M N e E) .fst (magmaequiv e E)

open MagmaΣTheory public using (InducedMagma; InducedMagmaPath)

MagmaPath : {M N : Magma ℓ} → (MagmaEquiv M N) ≃ (M ≡ N)
MagmaPath = MagmaΣTheory.MagmaPath _ _

open Magma

uaMagma : {M N : Magma ℓ} → MagmaEquiv M N → M ≡ N
uaMagma = equivFun MagmaPath

carac-uaMagma : {M N : Magma ℓ} (f : MagmaEquiv M N) → cong Carrier (uaMagma f) ≡ ua (MagmaEquiv.eq f)
carac-uaMagma (magmaequiv f m) =
  (refl ∙∙ ua f ∙∙ refl)
    ≡˘⟨ rUnit (ua f) ⟩
  ua f ∎



Magma≡ : (M N : Magma ℓ) → (
  Σ[ p ∈ ⟨ M ⟩ ≡ ⟨ N ⟩ ]
  Σ[ q ∈ PathP (λ i → p i → p i → p i) (_•_ M) (_•_ N) ]
  PathP (λ i → IsMagma (p i) (q i)) (isMagma M) (isMagma N))
  ≃ (M ≡ N)
Magma≡ M N = isoToEquiv (iso
  (λ (p , q , r) i → mkmagma (p i) (q i) (r i))
  (λ p → cong Carrier p , cong _•_ p , cong isMagma p)
  (λ _ → refl) (λ _ → refl))

caracMagma≡ : {M N : Magma ℓ} (p q : M ≡ N) → cong Carrier p ≡ cong Carrier q → p ≡ q
caracMagma≡ {M = M} {N} p q t = cong (Magma≡ M N .fst) (Σ≡Prop (λ _ →
    isPropΣ
    (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set N) _ _) λ _ →
    isOfHLevelPathP 1 (λ { (ismagma x) (ismagma y) → cong ismagma (isPropIsSet x y) }) _ _)
  t)

uaMagmaId : (M : Magma ℓ) → uaMagma (idMagmaEquiv M) ≡ refl
uaMagmaId M = caracMagma≡ _ _ (carac-uaMagma (idMagmaEquiv M) ∙ uaIdEquiv)

uaCompMagmaEquiv : {L M N : Magma ℓ} (f : MagmaEquiv L M) (g : MagmaEquiv M N) → uaMagma (compMagmaEquiv f g) ≡ uaMagma f ∙ uaMagma g
uaCompMagmaEquiv f g = caracMagma≡ _ _ (
  cong Carrier (uaMagma (compMagmaEquiv f g))
    ≡⟨ carac-uaMagma (compMagmaEquiv f g) ⟩
  ua (eq (compMagmaEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  ua (eq f) ∙ ua (eq g)
    ≡⟨ cong (_∙ ua (eq g)) (sym (carac-uaMagma f)) ⟩
  cong Carrier (uaMagma f) ∙ ua (eq g)
    ≡⟨ cong (cong Carrier (uaMagma f) ∙_) (sym (carac-uaMagma g)) ⟩
  cong Carrier (uaMagma f) ∙ cong Carrier (uaMagma g)
    ≡⟨ sym (cong-∙ Carrier (uaMagma f) (uaMagma g)) ⟩
  cong Carrier (uaMagma f ∙ uaMagma g) ∎)
  where open MagmaEquiv
