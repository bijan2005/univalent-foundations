{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra
open import Cubical.Algebra.Monoid.Morphism
open import Cubical.Algebra.Properties

open import Cubical.Relation.Binary.Reasoning.Equality

private
  variable
    g h : Level

-- The following definition of GroupHom and GroupEquiv are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.

record IsGroupHom (G : Group g) (H : Group h) (f : ⟨ G ⟩ → ⟨ H ⟩) : Type (ℓ-max g h) where
  constructor isgrouphom

  private
    module G = Group G
    module H = Group H

  field
    preservesOp : Homomorphic₂ f G._•_ H._•_

  preservesId : Homomorphic₀ f G.ε H.ε
  preservesId = H.cancelʳ _ (
    f G.ε H.• f G.ε ≡˘⟨ preservesOp G.ε G.ε ⟩
    f (G.ε G.• G.ε) ≡⟨ cong f (G.identityˡ G.ε) ⟩
    f G.ε           ≡˘⟨ H.identityˡ (f G.ε) ⟩
    H.ε H.• f G.ε   ∎)

  preservesInv : Homomorphic₁ f G._⁻¹ H._⁻¹
  preservesInv x = H.inv-uniqueʳ _ _ (
    f (x G.⁻¹) H.• f x ≡˘⟨ preservesOp (x G.⁻¹) x ⟩
    f (x G.⁻¹ G.• x)   ≡⟨ cong f (G.inverseˡ x) ⟩
    f G.ε              ≡⟨ preservesId ⟩
    H.ε                ∎)

record GroupHom (G : Group g) (H : Group h) : Type (ℓ-max g h) where
  constructor grouphom
  field
    fun : ⟨ G ⟩ → ⟨ H ⟩
    isHom : IsGroupHom G H fun

  open IsGroupHom isHom public

record GroupEquiv (G : Group g) (H : Group h) : Type (ℓ-max g h) where
  constructor groupequiv
  field
    eq : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : IsGroupHom G H (equivFun eq)

  open IsGroupHom isHom public

  hom : GroupHom G H
  hom = grouphom (equivFun eq) isHom


private
  variable
    G : Group g
    H : Group h

  isPropIsMonoidHom : {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (IsMonoidHom (Group.monoid G) (Group.monoid H) f)
  isPropIsMonoidHom {G = G} {H = H} {f = f} (ismonoidhom aOp aId) (ismonoidhom bOp bId) =
    cong₂ ismonoidhom
      (isPropHomomorphic₂ (Group.is-set H) f (Group._•_ G) (Group._•_ H) aOp bOp)
      (isPropHomomorphic₀ (Group.is-set H) f (Group.ε   G) (Group.ε   H) aId bId)

  isPropIsGroupHom : {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (IsGroupHom G H f)
  isPropIsGroupHom {G = G} {H = H} {f = f} (isgrouphom aHom) (isgrouphom bHom) =
    cong isgrouphom
      (isPropHomomorphic₂ (Group.is-set H) f (Group._•_ G) (Group._•_ H) aHom bHom)

IsGroupHom→IsMonoidHom : {f : ⟨ G ⟩ → ⟨ H ⟩} → IsGroupHom G H f → IsMonoidHom (Group.monoid G) (Group.monoid H) f
IsGroupHom→IsMonoidHom hom .IsMonoidHom.preservesOp = hom .IsGroupHom.preservesOp
IsGroupHom→IsMonoidHom hom .IsMonoidHom.preservesId = IsGroupHom.preservesId hom

IsMonoidHom→IsGroupHom : {f : ⟨ G ⟩ → ⟨ H ⟩} → IsMonoidHom (Group.monoid G) (Group.monoid H) f → IsGroupHom G H f
IsMonoidHom→IsGroupHom hom .IsGroupHom.preservesOp = hom .IsMonoidHom.preservesOp

IsGroupHom≃IsMonoidHom : {f : ⟨ G ⟩ → ⟨ H ⟩} → IsGroupHom G H f ≃ IsMonoidHom (Group.monoid G) (Group.monoid H) f
IsGroupHom≃IsMonoidHom {G = G} {H = H} = isoToEquiv
    (iso IsGroupHom→IsMonoidHom IsMonoidHom→IsGroupHom (λ _ → isPropIsMonoidHom {G = G} {H = H} _ _) (λ _ → isPropIsGroupHom _ _))


GroupHom→MonoidHom : GroupHom G H → MonoidHom (Group.monoid G) (Group.monoid H)
GroupHom→MonoidHom hom .MonoidHom.fun = hom .GroupHom.fun
GroupHom→MonoidHom hom .MonoidHom.isHom = IsGroupHom→IsMonoidHom (hom .GroupHom.isHom)

MonoidHom→GroupHom : MonoidHom (Group.monoid G) (Group.monoid H) → GroupHom G H
MonoidHom→GroupHom hom .GroupHom.fun = hom .MonoidHom.fun
MonoidHom→GroupHom hom .GroupHom.isHom = IsMonoidHom→IsGroupHom (hom .MonoidHom.isHom)

GroupHom≃MonoidHom : GroupHom G H ≃ MonoidHom (Group.monoid G) (Group.monoid H)
GroupHom≃MonoidHom {G = G} {H = H} =
    isoToEquiv (iso GroupHom→MonoidHom MonoidHom→GroupHom MonoidHom→GroupHom→MonoidHom GroupHom→MonoidHom→GroupHom)
  where
    MonoidHom→GroupHom→MonoidHom : section (GroupHom→MonoidHom {G = G} {H = H}) (MonoidHom→GroupHom {G = G} {H = H})
    MonoidHom→GroupHom→MonoidHom (monoidhom fun prf) = cong₂ monoidhom refl (isPropIsMonoidHom {G = G} {H = H} _ _)

    GroupHom→MonoidHom→GroupHom : retract (GroupHom→MonoidHom {G = G} {H = H}) (MonoidHom→GroupHom {G = G} {H = H})
    GroupHom→MonoidHom→GroupHom (grouphom fun prf) = cong₂ grouphom refl (isPropIsGroupHom _ _)


GroupEquiv→MonoidEquiv : GroupEquiv G H → MonoidEquiv (Group.monoid G) (Group.monoid H)
GroupEquiv→MonoidEquiv eq .MonoidEquiv.eq = eq .GroupEquiv.eq
GroupEquiv→MonoidEquiv eq .MonoidEquiv.isHom = IsGroupHom→IsMonoidHom (eq .GroupEquiv.isHom)

MonoidEquiv→GroupEquiv : MonoidEquiv (Group.monoid G) (Group.monoid H) → GroupEquiv G H
MonoidEquiv→GroupEquiv eq .GroupEquiv.eq = eq .MonoidEquiv.eq
MonoidEquiv→GroupEquiv eq .GroupEquiv.isHom = IsMonoidHom→IsGroupHom (eq .MonoidEquiv.isHom)

GroupEquiv≃MonoidEquiv : GroupEquiv G H ≃ MonoidEquiv (Group.monoid G) (Group.monoid H)
GroupEquiv≃MonoidEquiv {G = G} {H = H} =
    isoToEquiv (iso GroupEquiv→MonoidEquiv MonoidEquiv→GroupEquiv MonoidEquiv→GroupEquiv→MonoidEquiv GroupEquiv→MonoidEquiv→GroupEquiv)
  where
    MonoidEquiv→GroupEquiv→MonoidEquiv : section (GroupEquiv→MonoidEquiv {G = G} {H = H}) (MonoidEquiv→GroupEquiv {G = G} {H = H})
    MonoidEquiv→GroupEquiv→MonoidEquiv (monoidequiv eq prf) = cong₂ monoidequiv refl (isPropIsMonoidHom {G = G} {H = H} _ _)

    GroupEquiv→MonoidEquiv→GroupEquiv : retract (GroupEquiv→MonoidEquiv {G = G} {H = H}) (MonoidEquiv→GroupEquiv {G = G} {H = H})
    GroupEquiv→MonoidEquiv→GroupEquiv (groupequiv eq prf) = cong₂ groupequiv refl (isPropIsGroupHom _ _)
