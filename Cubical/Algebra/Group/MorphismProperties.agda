{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.MorphismProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_; id)
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Prod using (isPropProd)

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Group.Morphism

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Record

open import Cubical.Algebra.Monoid.Properties using (isPropIsMonoid)

open import Cubical.Relation.Binary.Reasoning.Equality

open Iso

private
  variable
    ℓ ℓ′ ℓ′′ : Level

isPropIsGroupHom : ∀ (G : Group ℓ) (H : Group ℓ′) f → isProp (IsGroupHom G H f)
isPropIsGroupHom G H f (isgrouphom aHom) (isgrouphom bHom) =
  cong isgrouphom
    (isPropHomomorphic₂ (Group.is-set H) f (Group._•_ G) (Group._•_ H) aHom bHom)

isSetGroupHom : {G : Group ℓ} {H : Group ℓ′} → isSet (GroupHom G H)
isSetGroupHom {G = G} {H = H} = isOfHLevelRespectEquiv 2 equiv (isSetΣ (isSetΠ λ _ → is-set H) (λ f → isProp→isSet (isPropIsGroupHom G H f)))
  where
    open Group
    equiv : (Σ[ g ∈ (⟨ G ⟩ → ⟨ H ⟩) ] IsGroupHom G H g) ≃ GroupHom G H
    equiv = isoToEquiv (iso (λ (g , m) → grouphom g m) (λ (grouphom g m) → g , m) (λ _ → refl) λ _ → refl)

isGroupHomComp : {F : Group ℓ} {G : Group ℓ′} {H : Group ℓ′′} {f : ⟨ F ⟩ → ⟨ G ⟩} {g : ⟨ G ⟩ → ⟨ H ⟩} →
                  IsGroupHom F G f → IsGroupHom G H g → IsGroupHom F H (g ∘ f)
isGroupHomComp {g = g} (isgrouphom fHom) (isgrouphom gHom) =
  isgrouphom (λ _ _ → cong g (fHom _ _) ∙ gHom _ _)

private
  isGroupHomComp′ : {F : Group ℓ} {G : Group ℓ′} {H : Group ℓ′′} (f : GroupHom F G) (g : GroupHom G H) →
                    IsGroupHom F H (GroupHom.fun g ∘ GroupHom.fun f)
  isGroupHomComp′ (grouphom f (isgrouphom fHom)) (grouphom g (isgrouphom gHom)) =
    isgrouphom (λ _ _ → cong g (fHom _ _) ∙ gHom _ _)

compGroupHom : {F : Group ℓ} {G : Group ℓ′} {H : Group ℓ′′} →
                GroupHom F G → GroupHom G H → GroupHom F H
compGroupHom {F = F} {G} {H} f g =
  grouphom _ (isGroupHomComp′ f g)

compGroupEquiv : {F : Group ℓ} {G : Group ℓ′} {H : Group ℓ′′} →
                  GroupEquiv F G → GroupEquiv G H → GroupEquiv F H
compGroupEquiv {F = F} {G} {H} f g = groupequiv (compEquiv f.eq g.eq) (isGroupHomComp′ f.hom g.hom)
  where
    module f = GroupEquiv f
    module g = GroupEquiv g

isGroupHomId : (G : Group ℓ) → IsGroupHom G G id
isGroupHomId G = record
  { preservesOp = λ _ _ → refl
  }

idGroupHom : (G : Group ℓ) → GroupHom G G
idGroupHom G = record
  { fun   = id
  ; isHom = isGroupHomId G
  }

idGroupEquiv : (G : Group ℓ) → GroupEquiv G G
idGroupEquiv G = record
  { eq    = idEquiv ⟨ G ⟩
  ; isHom = isGroupHomId G
  }

-- Isomorphism inversion
isGroupHomInv : {G : Group ℓ} {H : Group ℓ′} → (eqv : GroupEquiv G H) → IsGroupHom H G (invEq (GroupEquiv.eq eqv))
isGroupHomInv {G = G} {H} (groupequiv eq (isgrouphom hom)) = isgrouphom (λ x y → isInj-f (
    f (f⁻¹ (x H.• y))       ≡⟨ retEq eq _ ⟩
    x H.• y                 ≡˘⟨ cong₂ H._•_ (retEq eq x) (retEq eq y) ⟩
    f (f⁻¹ x) H.• f (f⁻¹ y) ≡˘⟨ hom (f⁻¹ x) (f⁻¹ y) ⟩
    f (f⁻¹ x G.• f⁻¹ y)     ∎))
    where
      module G = Group G
      module H = Group H
      f = equivFun eq
      f⁻¹ = invEq eq
      isInj-f : {x y : ⟨ G ⟩} → f x ≡ f y → x ≡ y
      isInj-f {x} {y} = invEq (_ , isEquiv→isEmbedding (eq .snd) x y)

invGroupHom : {G : Group ℓ} {H : Group ℓ′} → GroupEquiv G H → GroupHom H G
invGroupHom eq = record { isHom = isGroupHomInv eq }

invGroupEquiv : {G : Group ℓ} {H : Group ℓ′} → GroupEquiv G H → GroupEquiv H G
invGroupEquiv eq = record
  { eq    = invEquiv (GroupEquiv.eq eq)
  ; isHom = isGroupHomInv eq
  }

groupHomEq : {G : Group ℓ} {H : Group ℓ′} {f g : GroupHom G H} → (GroupHom.fun f ≡ GroupHom.fun g) → f ≡ g
groupHomEq {G = G} {H} {grouphom f fm} {grouphom g gm} p i = grouphom (p i) (p-hom i) where
  p-hom : PathP (λ i → IsGroupHom G H (p i)) fm gm
  p-hom = toPathP (isPropIsGroupHom G H _ _ _)

groupEquivEq : {G : Group ℓ} {H : Group ℓ′} {f g : GroupEquiv G H} → (GroupEquiv.eq f ≡ GroupEquiv.eq g) → f ≡ g
groupEquivEq {G = G} {H} {groupequiv f fm} {groupequiv g gm} p i = groupequiv (p i) (p-hom i) where
  p-hom : PathP (λ i → IsGroupHom G H (p i .fst)) fm gm
  p-hom = toPathP (isPropIsGroupHom G H _ _ _)

module GroupΣTheory {ℓ} where

  RawGroupStructure : Type ℓ → Type ℓ
  RawGroupStructure X = (X → X → X) × X × (X → X)

  RawGroupEquivStr = AutoEquivStr RawGroupStructure

  rawGroupUnivalentStr : UnivalentStr _ RawGroupEquivStr
  rawGroupUnivalentStr = autoUnivalentStr RawGroupStructure

  GroupAxioms : (G : Type ℓ) → RawGroupStructure G → Type ℓ
  GroupAxioms G (_•_ , ε , _⁻¹) = IsMonoid G _•_ ε × Inverse ε _⁻¹ _•_

  GroupStructure : Type ℓ → Type ℓ
  GroupStructure = AxiomsStructure RawGroupStructure GroupAxioms

  GroupΣ : Type (ℓ-suc ℓ)
  GroupΣ = TypeWithStr ℓ GroupStructure

  isPropGroupAxioms : (G : Type ℓ) (s : RawGroupStructure G) → isProp (GroupAxioms G s)
  isPropGroupAxioms G (_•_ , ε , _⁻¹) = isPropΣ isPropIsMonoid
                                    λ isMonG → isPropInverse (IsMonoid.is-set isMonG) _•_ _⁻¹ ε

  GroupEquivStr : StrEquiv GroupStructure ℓ
  GroupEquivStr = AxiomsEquivStr RawGroupEquivStr GroupAxioms

  GroupAxiomsIsoIsGroup : {G : Type ℓ} (s : RawGroupStructure G) →
                          Iso (GroupAxioms G s) (IsGroup G (s .fst) (s .snd .fst) (s .snd .snd))
  fun (GroupAxiomsIsoIsGroup s) (x , y)       = isgroup x y
  inv (GroupAxiomsIsoIsGroup s) (isgroup x y) = (x , y)
  rightInv (GroupAxiomsIsoIsGroup s) _        = refl
  leftInv (GroupAxiomsIsoIsGroup s) _         = refl

  GroupAxioms≡IsGroup : {G : Type ℓ} (s : RawGroupStructure G) →
                        GroupAxioms G s ≡ IsGroup G (s .fst) (s .snd .fst) (s .snd .snd)
  GroupAxioms≡IsGroup s = isoToPath (GroupAxiomsIsoIsGroup s)

  Group→GroupΣ : Group ℓ → GroupΣ
  Group→GroupΣ (mkgroup G _•_ ε _⁻¹ isGroup) =
    G , (_•_ , ε , _⁻¹) , GroupAxiomsIsoIsGroup (_•_ , ε , _⁻¹) .inv isGroup

  GroupΣ→Group : GroupΣ → Group ℓ
  GroupΣ→Group (G , (_•_ , ε , _⁻¹) , isGroupG) =
    mkgroup G _•_ ε _⁻¹ (GroupAxiomsIsoIsGroup (_•_ , ε , _⁻¹) .fun isGroupG)

  GroupIsoGroupΣ : Iso (Group ℓ) GroupΣ
  GroupIsoGroupΣ =
    iso Group→GroupΣ GroupΣ→Group (λ _ → refl) (λ _ → refl)

  groupUnivalentStr : UnivalentStr GroupStructure GroupEquivStr
  groupUnivalentStr = axiomsUnivalentStr _ isPropGroupAxioms rawGroupUnivalentStr

  GroupΣPath : (G H : GroupΣ) → (G ≃[ GroupEquivStr ] H) ≃ (G ≡ H)
  GroupΣPath = SIP groupUnivalentStr

  GroupEquivΣ : (G H : Group ℓ) → Type ℓ
  GroupEquivΣ G H = Group→GroupΣ G ≃[ GroupEquivStr ] Group→GroupΣ H

  GroupIsoΣPath : {G H : Group ℓ} → Iso (GroupEquiv G H) (GroupEquivΣ G H)
  fun GroupIsoΣPath (groupequiv eq hom) = eq , IsGroupHom.preservesOp hom , IsGroupHom.preservesId hom , IsGroupHom.preservesInv hom
  inv GroupIsoΣPath (eq , hom , _)      = groupequiv eq (isgrouphom hom)
  rightInv (GroupIsoΣPath {H = H}) _    = ΣPathTransport→PathΣ _ _ (refl ,
                                          ΣPathTransport→PathΣ _ _ (transportRefl _ ,
                                          ΣPathTransport→PathΣ _ _
                                          (Group.is-set H _ _ _ _ ,
                                          isPropΠ (λ _ → Group.is-set H _ _) _ _ )
                                          ))
  leftInv (GroupIsoΣPath {H = H}) _     = refl

  GroupPath : (G H : Group ℓ) → (GroupEquiv G H) ≃ (G ≡ H)
  GroupPath G H =
    GroupEquiv G H                   ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    GroupEquivΣ G H                  ≃⟨ GroupΣPath _ _ ⟩
    Group→GroupΣ G ≡ Group→GroupΣ H  ≃⟨ isoToEquiv (invIso (congIso GroupIsoGroupΣ)) ⟩
    G ≡ H                            ■

  RawGroupΣ : Type (ℓ-suc ℓ)
  RawGroupΣ = TypeWithStr ℓ RawGroupStructure

  Group→RawGroupΣ : Group ℓ → RawGroupΣ
  Group→RawGroupΣ (mkgroup A _•_ ε _⁻¹ _) = A , _•_ , ε , _⁻¹

  InducedGroup : (G : Group ℓ) (H : RawGroupΣ) (e : G .Group.Carrier ≃ H .fst)
                 → RawGroupEquivStr (Group→RawGroupΣ G) H e → Group ℓ
  InducedGroup G H e r =
    GroupΣ→Group (inducedStructure rawGroupUnivalentStr (Group→GroupΣ G) H (e , r))

  InducedGroupPath : (G : Group ℓ) (H : RawGroupΣ) (e : G .Group.Carrier ≃ H .fst)
                      (E : RawGroupEquivStr (Group→RawGroupΣ G) H e) →
                      G ≡ InducedGroup G H e E
  InducedGroupPath G H e E =
    GroupPath G (InducedGroup G H e E) .fst (groupequiv e (isgrouphom (E .fst)))

-- We now extract the important results from the above module

open GroupΣTheory public using (InducedGroup; InducedGroupPath)

isPropIsGroup : {G : Type ℓ} {_•_ : Op₂ G} {ε : G} {_⁻¹ : Op₁ G} → isProp (IsGroup G _•_ ε _⁻¹)
isPropIsGroup =
  subst isProp (GroupΣTheory.GroupAxioms≡IsGroup (_ , _ , _))
        (GroupΣTheory.isPropGroupAxioms _ (_ , _ , _))

GroupPath : {G H : Group ℓ} → (GroupEquiv G H) ≃ (G ≡ H)
GroupPath = GroupΣTheory.GroupPath _ _

open Group

uaGroup : {G H : Group ℓ} → GroupEquiv G H → G ≡ H
uaGroup = equivFun GroupPath

carac-uaGroup : {G H : Group ℓ} (f : GroupEquiv G H) → cong Carrier (uaGroup f) ≡ ua (GroupEquiv.eq f)
carac-uaGroup (groupequiv f m) =
  (refl ∙∙ ua f ∙∙ refl) ≡˘⟨ rUnit (ua f) ⟩
  ua f                   ∎

Group≡ : (G H : Group ℓ) → (
  Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ]
  Σ[ q ∈ PathP (λ i → p i → p i → p i) (_•_ G) (_•_ H) ]
  Σ[ r ∈ PathP (λ i → p i) (ε G) (ε H) ]
  Σ[ s ∈ PathP (λ i → p i → p i) (_⁻¹ G) (_⁻¹ H) ]
  PathP (λ i → IsGroup (p i) (q i) (r i) (s i)) (isGroup G) (isGroup H))
  ≃ (G ≡ H)
Group≡ G H = isoToEquiv (iso
  (λ (p , q , r , s , t) i → mkgroup (p i) (q i) (r i) (s i) (t i))
  (λ p → cong Carrier p , cong _•_ p , cong ε p , cong _⁻¹ p , cong isGroup p)
  (λ _ → refl) (λ _ → refl))

caracGroup≡ : {G H : Group ℓ} (p q : G ≡ H) → cong Carrier p ≡ cong Carrier q → p ≡ q
caracGroup≡ {G = G} {H} p q t = cong (fst (Group≡ G H)) (Σ≡Prop (λ _ → isPropΣ
    (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set H) _ _) λ _ → isPropΣ
    (isOfHLevelPathP' 1 (is-set H) _ _) λ _ → isPropΣ
    (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set H) _ _) λ _ →
    isOfHLevelPathP 1 isPropIsGroup _ _)
  t)

uaGroupId : (G : Group ℓ) → uaGroup (idGroupEquiv G) ≡ refl
uaGroupId G = caracGroup≡ _ _ (carac-uaGroup (idGroupEquiv G) ∙ uaIdEquiv)

uaCompGroupEquiv : {F G H : Group ℓ} (f : GroupEquiv F G) (g : GroupEquiv G H) → uaGroup (compGroupEquiv f g) ≡ uaGroup f ∙ uaGroup g
uaCompGroupEquiv f g = caracGroup≡ _ _ (
  cong Carrier (uaGroup (compGroupEquiv f g))
    ≡⟨ carac-uaGroup (compGroupEquiv f g) ⟩
  ua (eq (compGroupEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  ua (eq f) ∙ ua (eq g)
    ≡˘⟨ cong (_∙ ua (eq g)) (carac-uaGroup f) ⟩
  cong Carrier (uaGroup f) ∙ ua (eq g)
    ≡˘⟨ cong (cong Carrier (uaGroup f) ∙_) (carac-uaGroup g) ⟩
  cong Carrier (uaGroup f) ∙ cong Carrier (uaGroup g)
    ≡˘⟨ cong-∙ Carrier (uaGroup f) (uaGroup g) ⟩
  cong Carrier (uaGroup f ∙ uaGroup g) ∎)
  where open GroupEquiv
