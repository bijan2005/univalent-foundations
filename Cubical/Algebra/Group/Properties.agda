{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (flip)
open import Cubical.Functions.Embedding

open import Cubical.Data.Nat hiding (_+_; _*_)
open import Cubical.Data.NatPlusOne using (ℕ₊₁→ℕ)
open import Cubical.Data.Int
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Group.Morphism

open import Cubical.Algebra.Monoid.Properties using (isPropIsMonoid; module MonoidLemmas)

open import Cubical.Relation.Unary as Unary hiding (isPropValued)
open import Cubical.Relation.Binary as Binary hiding (isPropValued)
open import Cubical.Relation.Binary.Reasoning.Equality

open import Cubical.Algebra.Group.MorphismProperties public
  using (GroupPath; uaGroup; carac-uaGroup; Group≡; caracGroup≡)

private
  variable
    ℓ ℓ′ : Level

isPropIsGroup : ∀ {G : Type ℓ} {_•_ ε _⁻¹} → isProp (IsGroup G _•_ ε _⁻¹)
isPropIsGroup {G = G} {_•_} {ε} {_⁻¹} (isgroup aMon aInv) (isgroup bMon bInv) =
  cong₂ isgroup (isPropIsMonoid aMon bMon) (isPropInverse (IsMonoid.is-set aMon) _•_ _⁻¹ ε aInv bInv)

module GroupLemmas (G : Group ℓ) where
  open Group G

  open MonoidLemmas monoid public using (ε-comm) renaming (_^′_ to _^′′_; ^semi≡^ to ^semi≡^mon)

  invInvo : Involutive _⁻¹
  invInvo a = cancelʳ (a ⁻¹) (inverseˡ (a ⁻¹) ∙ sym (inverseʳ a))

  invId : ε ⁻¹ ≡ ε
  invId = cancelʳ ε (inverseˡ ε ∙ sym (identityʳ ε))

  invDistr : Homomorphic₂ _⁻¹ _•_ (flip _•_)
  invDistr x y = sym (inv-uniqueˡ _ _ (
    (x • y) • (y ⁻¹ • x ⁻¹)
      ≡˘⟨ assoc (x • y) (y ⁻¹) (x ⁻¹) ⟩
    x • y / y / x
      ≡⟨ cong (_/ x) (assoc _ _ _ ∙ cong (x •_) (inverseʳ y)) ⟩
    x • ε / x
      ≡⟨ cong (_/ x) (identityʳ x) ∙ inverseʳ x ⟩
    ε ∎))

  inv-comm : ∀ x → x • x ⁻¹ ≡ x ⁻¹ • x
  inv-comm x = inverseʳ x ∙ sym (inverseˡ x)


  isEquiv-•ˡ : ∀ x → isEquiv (x •_)
  isEquiv-•ˡ x = isoToIsEquiv (iso _ (x ⁻¹ •_) section-• retract-•)
    where
      section-• : section (x •_) (x ⁻¹ •_)
      section-• y =
        x • (x ⁻¹ • y) ≡˘⟨ assoc x (x ⁻¹) y ⟩
        x • x ⁻¹ • y   ≡⟨ cong (_• y) (inverseʳ x) ⟩
        ε • y          ≡⟨ identityˡ y ⟩
        y              ∎

      retract-• : retract (x •_) (x ⁻¹ •_)
      retract-• y =
        x ⁻¹ • (x • y) ≡˘⟨ assoc (x ⁻¹) x y ⟩
        x ⁻¹ • x • y   ≡⟨ cong (_• y) (inverseˡ x) ⟩
        ε • y          ≡⟨ identityˡ y ⟩
        y              ∎

  isEquiv-•ʳ : ∀ x → isEquiv (_• x)
  isEquiv-•ʳ x = isoToIsEquiv (iso _ (_• x ⁻¹) section-• retract-•)
    where
      section-• : section (_• x) (_• x ⁻¹)
      section-• y =
        y • x ⁻¹ • x   ≡⟨ assoc y (x ⁻¹) x ⟩
        y • (x ⁻¹ • x) ≡⟨ cong (y •_) (inverseˡ x) ⟩
        y • ε          ≡⟨ identityʳ y ⟩
        y              ∎

      retract-• : retract (_• x) (_• x ⁻¹)
      retract-• y =
        y • x • x ⁻¹   ≡⟨ assoc y x (x ⁻¹) ⟩
        y • (x • x ⁻¹) ≡⟨ cong (y •_) (inverseʳ x) ⟩
        y • ε          ≡⟨ identityʳ y ⟩
        y              ∎

  inv-≡ʳ : ∀ {x y} → x • y ⁻¹ ≡ ε → x ≡ y
  inv-≡ʳ p = inv-uniqueʳ _ _ p ∙ invInvo _

  inv-≡ˡ : ∀ {x y} → x ⁻¹ • y ≡ ε → x ≡ y
  inv-≡ˡ p = sym (invInvo _) ∙ sym (inv-uniqueˡ _ _ p)

  ≡-invʳ : ∀ {x y} → x ≡ y → x • y ⁻¹ ≡ ε
  ≡-invʳ p = subst (λ y → _ • y ⁻¹ ≡ ε) p (inverseʳ _)

  ≡-invˡ : ∀ {x y} → x ≡ y → x ⁻¹ • y ≡ ε
  ≡-invˡ p = subst (λ y → _ • y ≡ ε) p (inverseˡ _)


  ^-sucˡ : ∀ x n → x ^ sucInt n ≡ x • x ^ n
  ^-sucˡ x (pos n)                = refl
  ^-sucˡ x (negsuc zero)          = sym (inverseʳ x)
  ^-sucˡ x (negsuc (suc zero))    =
    x ^ -1          ≡⟨⟩
    x ⁻¹            ≡˘⟨ identityˡ _ ⟩
    ε • x ⁻¹        ≡˘⟨ cong (_• x ⁻¹) (inverseʳ x) ⟩
    x • x ⁻¹ • x ⁻¹ ≡⟨ assoc _ _ _ ⟩
    x • (x ^ -2)    ∎
  ^-sucˡ x (negsuc (suc (suc n))) =
    x ^ sucInt (negsuc (suc (suc n)))  ≡⟨⟩
    x ^ negsuc (suc n)                 ≡⟨⟩
    x ⁻¹ • x ^ negsuc n                ≡⟨⟩
    x ⁻¹ • x ^ sucInt (negsuc (suc n)) ≡⟨ cong (x ⁻¹ •_) (^-sucˡ x (negsuc (suc n))) ⟩
    x ⁻¹ • (x • x ^ negsuc (suc n))    ≡˘⟨ assoc _ _ _ ⟩
    x ⁻¹ • x • x ^ negsuc (suc n)      ≡˘⟨ cong (_• x ^ negsuc (suc n)) (inv-comm x) ⟩
    x • x ⁻¹ • x ^ negsuc (suc n)      ≡⟨ assoc _ _ _ ⟩
    x • (x ⁻¹ • x ^ negsuc (suc n))    ≡⟨⟩
    x • x ^ negsuc (suc (suc n))       ∎

  ^-sucʳ : ∀ x n → x ^ sucInt n ≡ x ^ n • x
  ^-sucʳ x (pos zero)       = ε-comm x
  ^-sucʳ x (pos (suc n))    =
    x ^ pos (suc (suc n)) ≡⟨⟩
    x • x ^ pos (suc n)   ≡⟨ cong (x •_) (^-sucʳ x (pos n)) ⟩
    x • (x ^ pos n • x)   ≡˘⟨ assoc _ _ _ ⟩
    x • x ^ pos n • x     ≡⟨⟩
    x ^ pos (suc n) • x   ∎
  ^-sucʳ x (negsuc zero)          = sym (inverseˡ x)
  ^-sucʳ x (negsuc (suc zero))    =
    x ⁻¹              ≡˘⟨ identityʳ _ ⟩
    x ⁻¹ • ε          ≡˘⟨ cong (x ⁻¹ •_) (inverseˡ x) ⟩
    x ⁻¹ • (x ⁻¹ • x) ≡˘⟨ assoc _ _ _ ⟩
    x ^ -2 • x        ∎
  ^-sucʳ x (negsuc (suc (suc n))) =
    x ^ sucInt (negsuc (suc (suc n)))  ≡⟨⟩
    x ^ negsuc (suc n)                 ≡⟨⟩
    x ⁻¹ • x ^ negsuc n                ≡⟨⟩
    x ⁻¹ • x ^ sucInt (negsuc (suc n)) ≡⟨ cong (x ⁻¹ •_) (^-sucʳ x (negsuc (suc n))) ⟩
    x ⁻¹ • (x ^ negsuc (suc n) • x)    ≡˘⟨ assoc _ _ _ ⟩
    x ⁻¹ • x ^ negsuc (suc n) • x      ≡⟨⟩
    x ^ negsuc (suc (suc n)) • x       ∎

  ^-predˡ : ∀ x n → x ^ predInt n ≡ x ⁻¹ • x ^ n
  ^-predˡ x (pos zero) = sym (identityʳ _)
  ^-predˡ x (pos (suc zero)) =
    ε              ≡˘⟨ inverseˡ x ⟩
    x ⁻¹ • x       ≡˘⟨ cong (x ⁻¹ •_) (identityʳ x) ⟩
    x ⁻¹ • (x • ε) ∎
  ^-predˡ x (pos (suc (suc n))) =
    x ^ predInt (pos (suc (suc n))) ≡⟨⟩
    x ^ pos (suc n)                 ≡⟨⟩
    x • x ^ pos n                   ≡⟨⟩
    x • x ^ predInt (pos (suc n))   ≡⟨ cong (x •_) (^-predˡ x (pos (suc n))) ⟩
    x • (x ⁻¹ • x ^ pos (suc n))    ≡˘⟨ assoc _ _ _ ⟩
    x • x ⁻¹ • x ^ pos (suc n)      ≡⟨ cong (_• x ^ pos (suc n)) (inv-comm x) ⟩
    x ⁻¹ • x • x ^ pos (suc n)      ≡⟨ assoc _ _ _ ⟩
    x ⁻¹ • (x • x ^ pos (suc n))    ≡⟨⟩
    x ⁻¹ • x ^ pos (suc (suc n))    ∎
  ^-predˡ x (negsuc n) = refl

  ^-predʳ : ∀ x n → x ^ predInt n ≡ x ^ n • x ⁻¹
  ^-predʳ x (pos zero) = sym (identityˡ _)
  ^-predʳ x (pos (suc zero)) =
    ε              ≡˘⟨ identityʳ _ ⟩
    ε • ε          ≡˘⟨ cong (ε •_) (inverseʳ _) ⟩
    ε • (x • x ⁻¹) ≡˘⟨ assoc _ _ _ ⟩
    ε • x • x ⁻¹   ≡˘⟨ cong (_• x ⁻¹) (ε-comm _) ⟩
    x • ε • x ⁻¹   ∎
  ^-predʳ x (pos (suc (suc n))) =
    x ^ predInt (pos (suc (suc n))) ≡⟨⟩
    x ^ pos (suc n)                 ≡⟨⟩
    x • x ^ pos n                   ≡⟨⟩
    x • x ^ predInt (pos (suc n))   ≡⟨ cong (x •_) (^-predʳ x (pos (suc n))) ⟩
    x • (x ^ pos (suc n) • x ⁻¹)    ≡˘⟨ assoc _ _ _ ⟩
    x • x ^ pos (suc n) • x ⁻¹      ≡⟨⟩
    x ^ pos (suc (suc n)) • x ⁻¹    ∎
  ^-predʳ x (negsuc zero) = refl
  ^-predʳ x (negsuc (suc n)) =
    x ^ predInt (negsuc (suc n))  ≡⟨⟩
    x ^ negsuc (suc (suc n))      ≡⟨⟩
    x ⁻¹ • x ^ negsuc (suc n)     ≡⟨⟩
    x ⁻¹ • x ^ predInt (negsuc n) ≡⟨ cong (x ⁻¹ •_) (^-predʳ x (negsuc n)) ⟩
    x ⁻¹ • (x ^ negsuc n • x ⁻¹)  ≡˘⟨ assoc _ _ _ ⟩
    x ⁻¹ • x ^ negsuc n • x ⁻¹    ≡⟨⟩
    x ^ negsuc (suc n) • x ⁻¹     ∎

  ^-plus : ∀ x → Homomorphic₂ (x ^_) _+_ _•_
  ^-plus x m (pos zero) = sym (identityʳ (x ^ m))
  ^-plus x m (pos (suc n)) =
    x ^ sucInt (m +pos n)   ≡⟨ ^-sucʳ x (m +pos n) ⟩
    x ^ (m +pos n) • x      ≡⟨ cong (_• x) (^-plus x m (pos n)) ⟩
    x ^ m • x ^ pos n • x   ≡⟨ assoc _ _ _ ⟩
    x ^ m • (x ^ pos n • x) ≡˘⟨ cong (x ^ m •_) (^-sucʳ x (pos n)) ⟩
    x ^ m • x ^ pos (suc n) ∎
  ^-plus x m (negsuc zero) = ^-predʳ x m
  ^-plus x m (negsuc (suc n)) =
    x ^ predInt (m +negsuc n)     ≡⟨ ^-predʳ x (m +negsuc n) ⟩
    x ^ (m +negsuc n) • x ⁻¹      ≡⟨ cong (_• x ⁻¹) (^-plus x m (negsuc n)) ⟩
    x ^ m • x ^ negsuc n • x ⁻¹   ≡⟨ assoc _ _ _ ⟩
    x ^ m • (x ^ negsuc n • x ⁻¹) ≡˘⟨ cong (x ^ m •_) (^-predʳ x (negsuc n)) ⟩
    x ^ m • x ^ negsuc (suc n)    ∎

  _^′_ : Carrier → ℕ → Carrier
  _^′_ = IsMonoid._^_ isMonoid

  ^mon≡^ : ∀ x n → x ^′ n ≡ x ^ pos n
  ^mon≡^ x zero = refl
  ^mon≡^ x (suc n) = cong (x •_) (^mon≡^ x n)

  ^semi≡^ : ∀ x n → x ^′′ n ≡ x ^ pos (ℕ₊₁→ℕ n)
  ^semi≡^ x n = ^semi≡^mon x n ∙ ^mon≡^ x (ℕ₊₁→ℕ n)

module Conjugation (G : Group ℓ) where
  open Group G
  open GroupLemmas G using (isEquiv-•ˡ; isEquiv-•ʳ)

  module _ (g : Carrier) where

    conjugate : Carrier → Carrier
    conjugate x = g • x • g ⁻¹

    conjugate-isEquiv : isEquiv conjugate
    conjugate-isEquiv = compIsEquiv (isEquiv-•ˡ g) (isEquiv-•ʳ (g ⁻¹))

    conjugate-hom : Homomorphic₂ conjugate _•_ _•_
    conjugate-hom x y =
      g • (x • y) • g ⁻¹              ≡˘⟨ cong (λ v → g • (v • y) • g ⁻¹) (identityʳ x) ⟩
      g • (x • ε • y) • g ⁻¹          ≡˘⟨ cong (λ v → g • (x • v • y) • g ⁻¹) (inverseˡ g) ⟩
      g • (x • (g ⁻¹ • g) • y) • g ⁻¹ ≡˘⟨ cong (λ v → g • (v • y) • g ⁻¹) (assoc _ _ _) ⟩
      g • (x • g ⁻¹ • g • y) • g ⁻¹   ≡˘⟨ cong (_• g ⁻¹) (assoc _ _ _) ⟩
      g • (x • g ⁻¹ • g) • y • g ⁻¹   ≡˘⟨ cong (λ v → v • y • g ⁻¹) (assoc _ _ _) ⟩
      g • (x • g ⁻¹) • g • y • g ⁻¹   ≡˘⟨ cong (λ v → v • g • y • g ⁻¹) (assoc _ _ _) ⟩
      g • x • g ⁻¹ • g • y • g ⁻¹     ≡⟨ cong (_• g ⁻¹) (assoc _ _ _) ⟩
      g • x • g ⁻¹ • (g • y) • g ⁻¹   ≡⟨ assoc _ _ _ ⟩
      g • x • g ⁻¹ • (g • y • g ⁻¹)   ∎

    conjugate-isHom : IsGroupHom G G conjugate
    conjugate-isHom = isgrouphom conjugate-hom

    conjugate-Hom : GroupHom G G
    conjugate-Hom = record { isHom = conjugate-isHom }

    conjugate-Equiv : GroupEquiv G G
    conjugate-Equiv = record { eq = conjugate , conjugate-isEquiv; isHom = conjugate-isHom }

    conjugate-Path : G ≡ G
    conjugate-Path = uaGroup conjugate-Equiv

  Conjugate : Rel Carrier ℓ
  Conjugate a b = Σ[ g ∈ Carrier ] conjugate g a ≡ b


module Normal (G : Group ℓ) where


module Kernel {G : Group ℓ} {H : Group ℓ′} (hom : GroupHom G H) where
  module G = Group G
  module H = Group H
  open GroupHom hom renaming (fun to f)
  open GroupLemmas


  Kernel : Pred ⟨ G ⟩ ℓ′
  Kernel x = f x ≡ H.ε

  isPropKernel : Unary.isPropValued Kernel
  isPropKernel x = H.is-set (f x) H.ε

  Kernelᵖ : PropPred ⟨ G ⟩ ℓ′
  Kernelᵖ = Kernel , isPropKernel


  ker-preservesId : G.ε ∈ Kernel
  ker-preservesId = preservesId

  ker-preservesOp : G._•_ Unary.Preserves₂ Kernel
  ker-preservesOp {x} {y} fx≡ε fy≡ε =
    f (x G.• y) ≡⟨ preservesOp x y ⟩
    f x H.• f y ≡⟨ cong₂ H._•_ fx≡ε fy≡ε ⟩
    H.ε H.• H.ε ≡⟨ H.identityʳ H.ε ⟩
    H.ε         ∎

  ker-preservesInv : G._⁻¹ Unary.Preserves Kernel
  ker-preservesInv {x} fx≡ε =
    f (x G.⁻¹) ≡⟨ preservesInv _ ⟩
    f x H.⁻¹   ≡⟨ cong H._⁻¹ fx≡ε ⟩
    H.ε H.⁻¹   ≡⟨ invId H ⟩
    H.ε        ∎


  ker⊆ε→inj : Kernel ⊆ ｛ G.ε ｝ → ∀ {x y} → f x ≡ f y → x ≡ y
  ker⊆ε→inj sub fx≡fy = inv-≡ʳ G (sub (preservesOp+Inv _ _ ∙ ≡-invʳ H fx≡fy))
    where
      preservesOp+Inv : ∀ a b → f (a G.• b G.⁻¹) ≡ f a H.• f b H.⁻¹
      preservesOp+Inv a b = preservesOp a (b G.⁻¹) ∙ cong (f a H.•_) (preservesInv b)

  ker⊆ε→emb : Kernel ⊆ ｛ G.ε ｝ → isEmbedding f
  ker⊆ε→emb sub = injEmbedding G.is-set H.is-set (ker⊆ε→inj sub)

  inj→ker⊆ε : (∀ {x y} → f x ≡ f y → x ≡ y) → Kernel ⊆ ｛ G.ε ｝
  inj→ker⊆ε inj fx≡ε = inj (fx≡ε ∙ sym preservesId)

  emb→ker⊆ε : isEmbedding f → Kernel ⊆ ｛ G.ε ｝
  emb→ker⊆ε emb = inj→ker⊆ε (invIsEq (emb _ _))


open GroupLemmas public
open Conjugation public
open Normal public
