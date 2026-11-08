{-# OPTIONS --safe --without-K #-}

-- Normalisation of the discrete model: `normH : M X ⇒ Prob X + 1`, built from a decision on the invertibility of
-- the mass (`InvDec`), with its invariance lemmas (`normProb`, `normZero`, `normScale`).
-- Second of three parts of the `StatisticalInterface` instance (`StatWeights`, `StatNormalize`, `StatInstance`).
module QBS.Model.StatNormalize where

open import Level using (Lift; lift)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Function.Construct.Composition as Comp

import Categories.Monad.Strong as CMS
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (_+Q_; Piece; ev)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (1Q)
open import QBS.Probability
open import QBS.Statistical
open import QBS.Model.Pairing
open import QBS.Model.DiscreteSource
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad
open import QBS.Model.WeightClasses
open import QBS.Model.Strong
open import QBS.Model.ProbInstance
open import QBS.Model.Cantor
open import QBS.Model.StatWeights

module StatNormalize {ℓ} (N : NormalizableSemiring ℓ) where
  open StatWeights N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  private
    open DS ℓ using (S)
    R = Lift ℓ ℕ
    r₀ : R
    r₀ = lift 0
  open Cantor A
  open QBS
  open Hom
  open MA using (Pre; mk; α; ∫; ∫ᶠ; mapPre; ηPre; joinPre; ∫-η; ∫-join; TQ; TH; TM; TF)
  open MA.Pre

  -- the interface (normalisation still to come)

  ----------------------------------------------------------------------------
  -- normalisation: M X ⇒ Prob X + 1

  mass : ∀ {X : QBS S} → Pre X → ∣A∣
  mass p = ∑ (μ p)

  oneF : ∀ (X : QBS S) → Func (Carrier X) Aˢ
  oneF X = record { to = λ _ → 1# ; cong = λ _ → refl }

  -- the mass is the integral of the constant 1
  mass≈∫ : ∀ {X : QBS S} (p : Pre X) → ∫ p (oneF X) ≈ mass p
  mass≈∫ p = ∑-cong (λ r → *-identityʳ _)

  mass-cong : ∀ {X : QBS S} {p q : Pre X} → MA._≈ᵖ_ p q → mass p ≈ mass q
  mass-cong {X} {p} {q} e = trans (sym (mass≈∫ p)) (trans (e (oneF X)) (mass≈∫ q))

  -- inverses are unique
  inv-unique : ∀ {m n n′} → m * n ≈ 1# → m * n′ ≈ 1# → n ≈ n′
  inv-unique {m} {n} {n′} h h′ = begin
    n              ≈⟨ sym (*-identityʳ n) ⟩
    n * 1#         ≈⟨ *-cong refl (sym h′) ⟩
    n * (m * n′)   ≈⟨ sym (*-assoc n m n′) ⟩
    (n * m) * n′   ≈⟨ *-cong (*-comm n m) refl ⟩
    (m * n) * n′   ≈⟨ *-cong h refl ⟩
    1# * n′        ≈⟨ *-identityˡ n′ ⟩
    n′             ∎
    where open SetoidReasoning Aˢ

  -- normalising by a given inverse of the mass
  normP : ∀ {X : QBS S} (n : ∣A∣) (p : Pre X) → mass p * n ≈ 1# → MP.Pre X
  normP n p h = MP.mk (αₛ p) (α-random p) (λ r → n * μ p r)
    (trans (∑-scale n (μ p)) (trans (*-comm n (mass p)) h))

  ∫-normP : ∀ {X : QBS S} n (p : Pre X) (h : mass p * n ≈ 1#) f →
    MP.∫ (normP n p h) f ≈ n * ∫ p f
  ∫-normP n p h f = ∫-scale n p f

  normC′ : ∀ {X : QBS S} (p : Pre X) → InvDec (mass p) → ∣ MP.TQ X ∣ ⊎ ⊤ {ℓ}
  normC′ p (inj₁ (n , h)) = inj₁ (normP n p h)
  normC′ p (inj₂ _) = inj₂ tt

  normC : ∀ {X : QBS S} → Pre X → ∣ MP.TQ X ∣ ⊎ ⊤ {ℓ}
  normC p = normC′ p (NormalizableSemiring.invertible? N (mass p))

  absurd : ∀ {B : Set ℓ} → ⊥ {ℓ} → B
  absurd {B} x = ⊥-elim {Whatever = λ _ → B} x

  normC-cong : ∀ {X : QBS S} {p q : Pre X} → MA._≈ᵖ_ p q →
    Setoid._≈_ (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S))) (normC p) (normC q)
  normC-cong {X} {p} {q} e with NormalizableSemiring.invertible? N (mass p) | NormalizableSemiring.invertible? N (mass q)
  ... | inj₁ (n , hn) | inj₁ (n′ , hn′) = ⊎ʳ.inj₁ (λ f →
        Setoid.trans Aˢ (∫-normP n p hn f)
          (Setoid.trans Aˢ (*-cong (inv-unique hn (trans (*-cong (mass-cong {X} {p} {q} e) refl) hn′)) (e f))
            (Setoid.sym Aˢ (∫-normP n′ q hn′ f))))
  ... | inj₁ (n , hn) | inj₂ r = absurd (r n (trans (*-cong (sym (mass-cong {X} {p} {q} e)) refl) hn))
  ... | inj₂ r | inj₁ (n′ , hn′) = absurd (r n′ (trans (*-cong (mass-cong {X} {p} {q} e) refl) hn′))
  ... | inj₂ _ | inj₂ _ = ⊎ʳ.inj₂ ≡.refl

  idx′ : ∀ {m} → InvDec m → ℕ
  idx′ (inj₁ _) = 0
  idx′ (inj₂ _) = 1

  dec : ∀ {X : QBS S} (β : R → Pre X) (r : R) → InvDec (mass (β r))
  dec β r = NormalizableSemiring.invertible? N (mass (β r))

  -- everything below is proved for an arbitrary decision function d, so that
  -- case analysis on `d r` never has to look inside definitions
  module _ {X : QBS S} {β : R → Pre X} (w : MA.Wit β) (d : ∀ r → InvDec (mass (β r))) where
    open MA.Wit w

    idxᵈ : R → ℕ
    idxᵈ r = idx′ (d r)

    massWg : ∀ r → ∑ (wg r) ≈ mass (β r)
    massWg r = sym (mass-cong {X} {β r} {mk {X} wαₛ wα-random (wg r) tt} (w-eq r))

    γ′ : ∀ r → InvDec (mass (β r)) → MP.Pre X
    γ′ r (inj₁ (n , h)) = normP n (β r) h
    γ′ r (inj₂ _) = MP.ηPre (wαₛ ⟨$⟩ r₀)

    wgγ′ : ∀ r → InvDec (mass (β r)) → R → ∣A∣
    wgγ′ r (inj₁ (n , _)) = λ k → n * wg r k
    wgγ′ r (inj₂ _) = dirac r₀

    wgγ-ok′ : ∀ r (e : InvDec (mass (β r))) → WeightClass.Ok (probClass A) (wgγ′ r e)
    wgγ-ok′ r (inj₁ (n , h)) = trans (∑-scale n (wg r))
                                 (trans (*-cong refl (massWg r)) (trans (*-comm n (mass (β r))) h))
    wgγ-ok′ r (inj₂ _) = WeightClass.ok-dirac (probClass A) r₀

    γ-eq′ : ∀ r (e : InvDec (mass (β r))) →
      MP._≈ᵖ_ (γ′ r e) (MP.mk {X} wαₛ wα-random (wgγ′ r e) (wgγ-ok′ r e))
    γ-eq′ r (inj₁ (n , h)) f =
      Setoid.trans Aˢ (∫-normP n (β r) h f)
        (Setoid.trans Aˢ (*-cong refl (w-eq r f))
          (Setoid.sym Aˢ (∫-scale n (mk {X} wαₛ wα-random (wg r) tt) f)))
    γ-eq′ r (inj₂ _) f =
      Setoid.trans Aˢ (MP.∫-η {X} (wαₛ ⟨$⟩ r₀) f) (Setoid.sym Aˢ (dirac-∑ r₀ (λ k → f ⟨$⟩ (wαₛ ⟨$⟩ k))))

    Wγ : MP.Wit (λ r → γ′ r (d r))
    Wγ = record
      { wαₛ = wαₛ ; wα-random = wα-random
      ; wg = λ r → wgγ′ r (d r) ; wg-ok = λ r → wgγ-ok′ r (d r)
      ; w-eq = λ r → γ-eq′ r (d r) }

    -- normalisation of a random family of measures is random in Prob + 1
    normRandomᵈ : QBS.Random (_+Q_ S (MP.TQ X) (1Q S)) (⇑ (λ r → normC′ (β r) (d r)))
    normRandomᵈ = ⇑ idxᵈ , tt , c , eq
      where
        c : ℕ → Piece S (MP.TQ X) (1Q S)
        c ℕ.zero = inj₁ (⇑ (λ r → γ′ r (d r)) , Wγ)
        c (ℕ.suc _) = inj₂ (constₛ tt , tt)

        eq : ∀ r → Setoid._≈_ (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S)))
               (normC′ (β r) (d r)) (ev S (MP.TQ X) (1Q S) (c (idx′ (d r))) r)
        eq r with d r in ed
        ... | inj₁ (n , h) = ⊎ʳ.inj₁ (≡.subst (λ e → MP._≈ᵖ_ (normP n (β r) h) (γ′ r e)) (≡.sym ed) (λ f → Setoid.refl Aˢ))
        ... | inj₂ _ = ⊎ʳ.inj₂ ≡.refl

  normRandom : ∀ {X : QBS S} {β : R → Pre X} → MA.Wit β →
    QBS.Random (_+Q_ S (MP.TQ X) (1Q S)) (⇑ (λ r → normC (β r)))
  normRandom {X} {β} w = normRandomᵈ w (λ r → NormalizableSemiring.invertible? N (mass (β r)))

  -- probability measures are fixed by normalisation
  normProb : ∀ {X : QBS S} (p : MP.Pre X) (e : InvDec (mass (forgetPre p))) →
    Setoid._≈_ (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S))) (normC′ (forgetPre p) e) (inj₁ p)
  normProb {X} p (inj₁ (n , h)) = ⊎ʳ.inj₁ (λ f →
    Setoid.trans Aˢ (∫-normP n (forgetPre p) h f)
      (Setoid.trans Aˢ (*-cong n≈1 (Setoid.refl Aˢ)) (*-identityˡ _)))
    where n≈1 = inv-unique {mass (forgetPre p)} h (trans (*-identityʳ _) (MP.Pre.μ-ok p))
  normProb p (inj₂ r) = absurd (r 1# (trans (*-identityʳ _) (MP.Pre.μ-ok p)))

  -- the zero measure normalises to failure
  normZero : ∀ {X : QBS S} (p : Pre X) → mass p ≈ 0# → (e : InvDec (mass p)) →
    Setoid._≈_ (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S))) (normC′ p e) (inj₂ tt)
  normZero p z (inj₁ (n , h)) =
    absurd (NormalizableSemiring.nontrivial N
      (trans (sym (zeroˡ n)) (trans (*-cong (sym z) refl) h)))
  normZero p z (inj₂ _) = ⊎ʳ.inj₂ ≡.refl

  mass-scale : ∀ {X : QBS S} c (p : Pre X) → mass (scaleP c p) ≈ c * mass p
  mass-scale c p = ∑-scale c (μ p)

  -- if (c m) n′ ≈ 1 then n′ c is an inverse of m
  inv-of-scaled : ∀ {c m n′} → (c * m) * n′ ≈ 1# → m * (n′ * c) ≈ 1#
  inv-of-scaled {c} {m} {n′} h = begin
    m * (n′ * c)    ≈⟨ *-cong refl (*-comm n′ c) ⟩
    m * (c * n′)    ≈⟨ sym (*-assoc m c n′) ⟩
    (m * c) * n′    ≈⟨ *-cong (*-comm m c) refl ⟩
    (c * m) * n′    ≈⟨ h ⟩
    1#              ∎
    where open SetoidReasoning Aˢ

  -- if m n ≈ 1 and c d ≈ 1 then (c m) (n d) ≈ 1
  inv-scaled : ∀ {c d m n} → c * d ≈ 1# → m * n ≈ 1# → (c * m) * (n * d) ≈ 1#
  inv-scaled {c} {d} {m} {n} cd mn = begin
    (c * m) * (n * d)    ≈⟨ *-assoc c m (n * d) ⟩
    c * (m * (n * d))    ≈⟨ *-cong refl (sym (*-assoc m n d)) ⟩
    c * ((m * n) * d)    ≈⟨ *-cong refl (*-cong mn refl) ⟩
    c * (1# * d)         ≈⟨ *-cong refl (*-identityˡ d) ⟩
    c * d                ≈⟨ cd ⟩
    1#                   ∎
    where open SetoidReasoning Aˢ

  -- normalisation is invariant under scaling by an invertible weight
  normScale : ∀ {X : QBS S} (c d : ∣A∣) → c * d ≈ 1# → (p : Pre X)
    (e′ : InvDec (mass (scaleP c p))) (e : InvDec (mass p)) →
    Setoid._≈_ (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S))) (normC′ (scaleP c p) e′) (normC′ p e)
  normScale {X} c d cd p (inj₁ (n′ , hn′)) (inj₁ (n , hn)) = ⊎ʳ.inj₁ (λ f →
    Setoid.trans Aˢ (∫-normP n′ (scaleP c p) hn′ f)
      (Setoid.trans Aˢ (*-cong refl (∫-scale c p f))
        (Setoid.trans Aˢ (sym (*-assoc n′ c (∫ p f)))
          (Setoid.trans Aˢ (*-cong n′c≈n refl) (Setoid.sym Aˢ (∫-normP n p hn f))))))
    where
      n′c≈n : n′ * c ≈ n
      n′c≈n = inv-unique {mass p} (inv-of-scaled (trans (*-cong (sym (mass-scale c p)) refl) hn′)) hn
  normScale c d cd p (inj₁ (n′ , hn′)) (inj₂ r) =
    absurd (r (n′ * c) (inv-of-scaled (trans (*-cong (sym (mass-scale c p)) refl) hn′)))
  normScale c d cd p (inj₂ r′) (inj₁ (n , hn)) =
    absurd (r′ (n * d) (trans (*-cong (mass-scale c p) refl) (inv-scaled cd hn)))
  normScale c d cd p (inj₂ _) (inj₂ _) = ⊎ʳ.inj₂ ≡.refl

  normH : ∀ X → Hom S (MA.TQ X) (_+Q_ S (MP.TQ X) (1Q S))
  normH X = record
    { map = record { to = normC ; cong = normC-cong }
    ; map-random = normRandom
    }
