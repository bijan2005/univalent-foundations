{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Monoid.MorphismProperties where

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
open import Cubical.Algebra.Monoid.Morphism

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Pointed

open import Cubical.Algebra.Semigroup.Properties using (isPropIsSemigroup)

open import Cubical.Relation.Binary.Reasoning.Equality

open Iso

private
  variable
    ℓ ℓ′ ℓ′′ : Level

isPropIsMonoidHom : ∀ (M : Monoid ℓ) (N : Monoid ℓ′) f → isProp (IsMonoidHom M N f)
isPropIsMonoidHom M N f (ismonoidhom aOp aId) (ismonoidhom bOp bId) =
  cong₂ ismonoidhom
    (isPropHomomorphic₂ (Monoid.is-set N) f (Monoid._•_ M) (Monoid._•_ N) aOp bOp)
    (isPropHomomorphic₀ (Monoid.is-set N) f (Monoid.ε   M) (Monoid.ε   N) aId bId)

isSetMonoidHom : {M : Monoid ℓ} {N : Monoid ℓ′} → isSet (MonoidHom M N)
isSetMonoidHom {M = M} {N = N} = isOfHLevelRespectEquiv 2 equiv (isSetΣ (isSetΠ λ _ → is-set N) (λ f → isProp→isSet (isPropIsMonoidHom M N f)))
  where
    open Monoid
    equiv : (Σ[ g ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsMonoidHom M N g) ≃ MonoidHom M N
    equiv = isoToEquiv (iso (λ (g , m) → monoidhom g m) (λ (monoidhom g m) → g , m) (λ _ → refl) λ _ → refl)

isMonoidHomComp : {L : Monoid ℓ} {M : Monoid ℓ′} {N : Monoid ℓ′′} {f : ⟨ L ⟩ → ⟨ M ⟩} {g : ⟨ M ⟩ → ⟨ N ⟩} →
                  IsMonoidHom L M f → IsMonoidHom M N g → IsMonoidHom L N (g ∘ f)
isMonoidHomComp {g = g} (ismonoidhom fOp fId) (ismonoidhom gOp gId) =
  ismonoidhom (λ _ _ → cong g (fOp _ _) ∙ gOp _ _) (cong g fId ∙ gId)

private
  isMonoidHomComp′ : {L : Monoid ℓ} {M : Monoid ℓ′} {N : Monoid ℓ′′} (f : MonoidHom L M) (g : MonoidHom M N) →
                    IsMonoidHom L N (MonoidHom.fun g ∘ MonoidHom.fun f)
  isMonoidHomComp′ (monoidhom f (ismonoidhom fOp fId)) (monoidhom g (ismonoidhom gOp gId)) =
    ismonoidhom (λ _ _ → cong g (fOp _ _) ∙ gOp _ _) (cong g fId ∙ gId)

compMonoidHom : {L : Monoid ℓ} {M : Monoid ℓ′} {N : Monoid ℓ′′} →
                MonoidHom L M → MonoidHom M N → MonoidHom L N
compMonoidHom {L = L} {M} {N} f g =
  monoidhom _ (isMonoidHomComp′ f g)

compMonoidEquiv : {L : Monoid ℓ} {M : Monoid ℓ′′} {N : Monoid ℓ′′} →
                  MonoidEquiv L M → MonoidEquiv M N → MonoidEquiv L N
compMonoidEquiv {L = L} {M} {N} f g = monoidequiv (compEquiv f.eq g.eq) (isMonoidHomComp′ f.hom g.hom)
  where
    module f = MonoidEquiv f
    module g = MonoidEquiv g

isMonoidHomId : (M : Monoid ℓ) → IsMonoidHom M M id
isMonoidHomId M = record
  { preservesOp = λ _ _ → refl
  ; preservesId = refl
  }

idMonoidHom : (M : Monoid ℓ) → MonoidHom M M
idMonoidHom M = record
  { fun   = id
  ; isHom = isMonoidHomId M
  }

idMonoidEquiv : (M : Monoid ℓ) → MonoidEquiv M M
idMonoidEquiv M = record
  { eq    = idEquiv ⟨ M ⟩
  ; isHom = isMonoidHomId M
  }

-- Isomorphism inversion
isMonoidHomInv : {M : Monoid ℓ} {N : Monoid ℓ′} → (eqv : MonoidEquiv M N) → IsMonoidHom N M (invEq (MonoidEquiv.eq eqv))
isMonoidHomInv {M = M} {N} (monoidequiv eq (ismonoidhom hOp hId)) = ismonoidhom
  (λ x y → isInj-f (
    f (f⁻¹ (x N.• y))       ≡⟨ retEq eq _ ⟩
    x N.• y                 ≡˘⟨ cong₂ N._•_ (retEq eq x) (retEq eq y) ⟩
    f (f⁻¹ x) N.• f (f⁻¹ y) ≡˘⟨ hOp (f⁻¹ x) (f⁻¹ y) ⟩
    f (f⁻¹ x M.• f⁻¹ y)     ∎))
  (isInj-f (
    f (f⁻¹ N.ε) ≡⟨ retEq eq _ ⟩
    N.ε         ≡˘⟨ hId ⟩
    f M.ε       ∎))
    where
      module M = Monoid M
      module N = Monoid N
      f = equivFun eq
      f⁻¹ = invEq eq
      isInj-f : {x y : ⟨ M ⟩} → f x ≡ f y → x ≡ y
      isInj-f {x} {y} = invEq (_ , isEquiv→isEmbedding (eq .snd) x y)

invMonoidHom : {M : Monoid ℓ} {N : Monoid ℓ′} → MonoidEquiv M N → MonoidHom N M
invMonoidHom eq = record { isHom = isMonoidHomInv eq }

invMonoidEquiv : {M : Monoid ℓ} {N : Monoid ℓ′} → MonoidEquiv M N → MonoidEquiv N M
invMonoidEquiv eq = record
  { eq    = invEquiv (MonoidEquiv.eq eq)
  ; isHom = isMonoidHomInv eq
  }

monoidHomEq : {M : Monoid ℓ} {N : Monoid ℓ′} {f g : MonoidHom M N} → MonoidHom.fun f ≡ MonoidHom.fun g → f ≡ g
monoidHomEq {M = M} {N} {monoidhom f fm} {monoidhom g gm} p i = monoidhom (p i) (p-hom i)
  where
    p-hom : PathP (λ i → IsMonoidHom M N (p i)) fm gm
    p-hom = toPathP (isPropIsMonoidHom M N _ _ _)

monoidEquivEq : {M : Monoid ℓ} {N : Monoid ℓ′} {f g : MonoidEquiv M N} → MonoidEquiv.eq f ≡ MonoidEquiv.eq g → f ≡ g
monoidEquivEq {M = M} {N} {monoidequiv f fm} {monoidequiv g gm} p i = monoidequiv (p i) (p-hom i)
  where
    p-hom : PathP (λ i → IsMonoidHom M N (p i .fst)) fm gm
    p-hom = toPathP (isPropIsMonoidHom M N _ _ _)

module MonoidΣTheory {ℓ} where

  RawMonoidStructure : Type ℓ → Type ℓ
  RawMonoidStructure X = (X → X → X) × X

  RawMonoidEquivStr = AutoEquivStr RawMonoidStructure

  rawMonoidUnivalentStr : UnivalentStr _ RawMonoidEquivStr
  rawMonoidUnivalentStr = autoUnivalentStr RawMonoidStructure

  MonoidAxioms : (M : Type ℓ) → RawMonoidStructure M → Type ℓ
  MonoidAxioms M (_•_ , ε) = IsSemigroup M _•_ × Identity ε _•_

  MonoidStructure : Type ℓ → Type ℓ
  MonoidStructure = AxiomsStructure RawMonoidStructure MonoidAxioms

  MonoidΣ : Type (ℓ-suc ℓ)
  MonoidΣ = TypeWithStr ℓ MonoidStructure

  isPropMonoidAxioms : (M : Type ℓ) (s : RawMonoidStructure M) → isProp (MonoidAxioms M s)
  isPropMonoidAxioms M (_•_ , ε) = isPropΣ isPropIsSemigroup
                                    λ isSemiM → isPropIdentity (IsSemigroup.is-set isSemiM) _•_ ε

  MonoidEquivStr : StrEquiv MonoidStructure ℓ
  MonoidEquivStr = AxiomsEquivStr RawMonoidEquivStr MonoidAxioms

  MonoidAxiomsIsoIsMonoid : {M : Type ℓ} (s : RawMonoidStructure M) →
                            Iso (MonoidAxioms M s) (IsMonoid M (s .fst) (s .snd))
  fun (MonoidAxiomsIsoIsMonoid s) (x , y)        = ismonoid x y
  inv (MonoidAxiomsIsoIsMonoid s) (ismonoid x y) = (x , y)
  rightInv (MonoidAxiomsIsoIsMonoid s) _         = refl
  leftInv (MonoidAxiomsIsoIsMonoid s) _          = refl

  MonoidAxioms≡IsMonoid : {M : Type ℓ} (s : RawMonoidStructure M) →
                          MonoidAxioms M s ≡ IsMonoid M (s .fst) (s .snd)
  MonoidAxioms≡IsMonoid s = isoToPath (MonoidAxiomsIsoIsMonoid s)

  Monoid→MonoidΣ : Monoid ℓ → MonoidΣ
  Monoid→MonoidΣ (mkmonoid M _•_ ε isMonoidM) =
    M , (_•_ , ε) , MonoidAxiomsIsoIsMonoid (_•_ , ε) .inv isMonoidM

  MonoidΣ→Monoid : MonoidΣ → Monoid ℓ
  MonoidΣ→Monoid (M , (_•_ , ε) , isMonoidM) =
    mkmonoid M _•_ ε (MonoidAxiomsIsoIsMonoid (_•_ , ε) .fun isMonoidM)

  MonoidIsoMonoidΣ : Iso (Monoid ℓ) MonoidΣ
  MonoidIsoMonoidΣ =
    iso Monoid→MonoidΣ MonoidΣ→Monoid (λ _ → refl) (λ _ → refl)

  monoidUnivalentStr : UnivalentStr MonoidStructure MonoidEquivStr
  monoidUnivalentStr = axiomsUnivalentStr _ isPropMonoidAxioms rawMonoidUnivalentStr

  MonoidΣPath : (M N : MonoidΣ) → (M ≃[ MonoidEquivStr ] N) ≃ (M ≡ N)
  MonoidΣPath = SIP monoidUnivalentStr

  MonoidEquivΣ : (M N : Monoid ℓ) → Type ℓ
  MonoidEquivΣ M N = Monoid→MonoidΣ M ≃[ MonoidEquivStr ] Monoid→MonoidΣ N

  MonoidIsoΣPath : {M N : Monoid ℓ} → Iso (MonoidEquiv M N) (MonoidEquivΣ M N)
  fun MonoidIsoΣPath (monoidequiv eq (ismonoidhom hOp hId)) = (eq , hOp , hId)
  inv MonoidIsoΣPath (eq , hOp , hId)                       = monoidequiv eq (ismonoidhom hOp hId)
  rightInv MonoidIsoΣPath _                                 = refl
  leftInv MonoidIsoΣPath _                                  = refl

  MonoidPath : (M N : Monoid ℓ) → (MonoidEquiv M N) ≃ (M ≡ N)
  MonoidPath M N =
    MonoidEquiv M N                       ≃⟨ isoToEquiv MonoidIsoΣPath ⟩
    MonoidEquivΣ M N                      ≃⟨ MonoidΣPath _ _ ⟩
    Monoid→MonoidΣ M ≡ Monoid→MonoidΣ N   ≃⟨ isoToEquiv (invIso (congIso MonoidIsoMonoidΣ)) ⟩
    M ≡ N                                 ■

  RawMonoidΣ : Type (ℓ-suc ℓ)
  RawMonoidΣ = TypeWithStr ℓ RawMonoidStructure

  Monoid→RawMonoidΣ : Monoid ℓ → RawMonoidΣ
  Monoid→RawMonoidΣ (mkmonoid A _•_ ε _) = A , _•_ , ε

  InducedMonoid : (M : Monoid ℓ) (N : RawMonoidΣ) (e : M .Monoid.Carrier ≃ N .fst) →
                  RawMonoidEquivStr (Monoid→RawMonoidΣ M) N e → Monoid ℓ
  InducedMonoid M N e r =
    MonoidΣ→Monoid (inducedStructure rawMonoidUnivalentStr (Monoid→MonoidΣ M) N (e , r))

  InducedMonoidPath : (M : Monoid ℓ) (N : RawMonoidΣ) (e : M .Monoid.Carrier ≃ N .fst)
                      (E : RawMonoidEquivStr (Monoid→RawMonoidΣ M) N e) →
                      M ≡ InducedMonoid M N e E
  InducedMonoidPath M N e E =
    MonoidPath M (InducedMonoid M N e E) .fst (monoidequiv e (ismonoidhom (E .fst) (E .snd)))

-- We now extract the important results from the above module

open MonoidΣTheory public using (InducedMonoid; InducedMonoidPath)

isPropIsMonoid : {M : Type ℓ} {_•_ : Op₂ M} {ε : M} → isProp (IsMonoid M _•_ ε)
isPropIsMonoid {_•_ = _•_} {ε} =
  subst isProp (MonoidΣTheory.MonoidAxioms≡IsMonoid (_•_ , ε))
        (MonoidΣTheory.isPropMonoidAxioms _ (_•_ , ε))

MonoidPath : {M N : Monoid ℓ} → (MonoidEquiv M N) ≃ (M ≡ N)
MonoidPath {M = M} {N} = MonoidΣTheory.MonoidPath M N

open Monoid

uaMonoid : {M N : Monoid ℓ} → MonoidEquiv M N → M ≡ N
uaMonoid = equivFun MonoidPath

carac-uaMonoid : {M N : Monoid ℓ} (f : MonoidEquiv M N) → cong Carrier (uaMonoid f) ≡ ua (MonoidEquiv.eq f)
carac-uaMonoid (monoidequiv f m) =
  (refl ∙∙ ua f ∙∙ refl)  ≡˘⟨ rUnit (ua f) ⟩
  ua f                    ∎

Monoid≡ : (M N : Monoid ℓ) → (
  Σ[ p ∈ ⟨ M ⟩ ≡ ⟨ N ⟩ ]
  Σ[ q ∈ PathP (λ i → p i → p i → p i) (_•_ M) (_•_ N) ]
  Σ[ r ∈ PathP (λ i → p i) (ε M) (ε N) ]
  PathP (λ i → IsMonoid (p i) (q i) (r i)) (isMonoid M) (isMonoid N))
  ≃ (M ≡ N)
Monoid≡ M N = isoToEquiv (iso
  (λ (p , q , r , s) i → mkmonoid (p i) (q i) (r i) (s i))
  (λ p → cong Carrier p , cong _•_ p , cong ε p , cong isMonoid p)
  (λ _ → refl) (λ _ → refl))

caracMonoid≡ : {M N : Monoid ℓ} (p q : M ≡ N) → cong Carrier p ≡ cong Carrier q → p ≡ q
caracMonoid≡ {M = M} {N} p q t = cong (fst (Monoid≡ M N)) (Σ≡Prop (λ _ →
    isPropΣ
    (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set N) _ _) λ _ → isPropΣ
    (isOfHLevelPathP' 1 (is-set N) _ _) λ _ →
    isOfHLevelPathP 1 isPropIsMonoid _ _)
  t)

uaMonoidId : (M : Monoid ℓ) → uaMonoid (idMonoidEquiv M) ≡ refl
uaMonoidId M = caracMonoid≡ _ _ (carac-uaMonoid (idMonoidEquiv M) ∙ uaIdEquiv)

uaCompMonoidEquiv : {L M N : Monoid ℓ} (f : MonoidEquiv L M) (g : MonoidEquiv M N) → uaMonoid (compMonoidEquiv f g) ≡ uaMonoid f ∙ uaMonoid g
uaCompMonoidEquiv f g = caracMonoid≡ _ _ (
  cong Carrier (uaMonoid (compMonoidEquiv f g))
    ≡⟨ carac-uaMonoid (compMonoidEquiv f g) ⟩
  ua (eq (compMonoidEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  ua (eq f) ∙ ua (eq g)
    ≡˘⟨ cong (_∙ ua (eq g)) (carac-uaMonoid f) ⟩
  cong Carrier (uaMonoid f) ∙ ua (eq g)
    ≡˘⟨ cong (cong Carrier (uaMonoid f) ∙_) (carac-uaMonoid g) ⟩
  cong Carrier (uaMonoid f) ∙ cong Carrier (uaMonoid g)
    ≡˘⟨ cong-∙ Carrier (uaMonoid f) (uaMonoid g) ⟩
  cong Carrier (uaMonoid f ∙ uaMonoid g) ∎)
  where open MonoidEquiv
