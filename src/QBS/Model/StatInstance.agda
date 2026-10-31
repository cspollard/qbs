{-# OPTIONS --safe --without-K #-}

-- The discrete measure monad is a model of `StatisticalInterface`.
module QBS.Model.StatInstance where

open import Level using (Level; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Function.Construct.Composition as Comp

open import Categories.Category.Core using (Category)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import Categories.Monad using (Monad)
import Categories.Monad.Strong as CMS
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Functor using (Functor)
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (cocartesian; _+Q_; Piece; ev)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; !Q)
open import QBS.Exponential using (cartesianClosed)
open import QBS.Probes using (ℛQ; probe; unprobe)
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

module _ {ℓ} (N : NormalizableSemiring ℓ) where
  A = NormalizableSemiring.complete N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  private
    open DS ℓ using (S)
    R = Lift ℓ ℕ
  open Cantor A
  module MA = Measures A (allClass A)
  module MP = Measures A (probClass A)
  open QBS
  open Hom

  -- The weights object: A itself, with every function random.
  WQ : QBS S
  WQ = record
    { Carrier = Aˢ
    ; probes = record
        { Random = λ _ → ⊤
        ; random-resp = λ _ _ → tt
        ; const-random = λ _ → tt
        ; pre-random = λ _ _ → tt
        }
    ; glue-random = λ _ _ _ → tt
    }

  mulH : Hom S (_×Q_ S WQ WQ) WQ
  mulH = record
    { map = record { to = λ p → proj₁ p * proj₂ p ; cong = λ { (e₁ , e₂) → *-cong e₁ e₂ } }
    ; map-random = λ _ → tt
    }

  constH : ∣A∣ → Hom S (1Q S) WQ
  constH a = record
    { map = record { to = λ _ → a ; cong = λ _ → Setoid.refl Aˢ }
    ; map-random = λ _ → tt
    }

  ----------------------------------------------------------------------------
  -- Prob ⊆ M

  forgetPre : ∀ {X : QBS S} → MP.Pre X → MA.Pre X
  forgetPre p = MA.mk (MP.Pre.α p) (MP.Pre.α-random p) (MP.Pre.μ p) tt

  inclH : ∀ X → Hom S (MP.TQ X) (MA.TQ X)
  inclH X = record
    { map = record { to = forgetPre ; cong = λ e f → e f }
    ; map-random = λ {β} w → record
        { wα = MP.Wit.wα w
        ; wα-random = MP.Wit.wα-random w
        ; wg = MP.Wit.wg w
        ; wg-ok = λ _ → tt
        ; w-eq = λ r f → MP.Wit.w-eq w r f
        }
    }

  inclN : NaturalTransformation MP.TF MA.TF
  inclN = record
    { η = inclH
    ; commute = λ _ _ _ → Setoid.refl Aˢ
    ; sym-commute = λ _ _ _ → Setoid.refl Aˢ
    }

  inclusion : Monad⇒-id MA.TM MP.TM
  inclusion = record
    { α = inclN
    ; unit-comp = λ _ _ → Setoid.refl Aˢ
    ; mult-comp = λ {U} p f →
        Setoid.trans Aˢ (MP.∫-join p f)
          (Setoid.sym Aˢ (MA.∫-join (forgetPre (MP.mapPre (inclH U) p)) f))
    }

  ----------------------------------------------------------------------------
  -- zero, score, scaling and countable sums on the measure monad M

  private
    r₀ : R
    r₀ = lift 0

  open MA using (⇑; Pre; mk; ∫; ∫ᶠ; mapPre; ηPre; joinPre; ∫-η; ∫-join; TQ; TH; TM; TF)
  open MA.Pre

  -- constant elements ⊤ ⇒ M X
  constE : ∀ {X : QBS S} → Pre X → Hom S (1Q S) (TQ X)
  constE {X} p = record
    { map = record { to = λ _ → p ; cong = λ _ _ → Setoid.refl Aˢ }
    ; map-random = λ _ → QBS.const-random (TQ X) p
    }

  zeroP : Pre (1Q S)
  zeroP = mk (const tt) tt (λ _ → 0#) tt

  ∫-zero : ∀ f → ∫ zeroP f ≈ 0#
  ∫-zero f = ∑-zero _ (λ _ → zeroˡ _)

  scoreP : ∣A∣ → Pre (1Q S)
  scoreP a = mk (const tt) tt (λ r → a * dirac r₀ r) tt

  weight-sum : ∀ a c → ∑ (λ r → (a * dirac r₀ r) * c) ≈ a * c
  weight-sum a c = begin
    ∑ (λ r → (a * dirac r₀ r) * c)    ≈⟨ ∑-cong (λ r → *-assoc a (dirac r₀ r) c) ⟩
    ∑ (λ r → a * (dirac r₀ r * c))    ≈⟨ ∑-scale a (λ r → dirac r₀ r * c) ⟩
    a * ∑ (λ r → dirac r₀ r * c)      ≈⟨ *-cong refl (dirac-∑ r₀ (λ _ → c)) ⟩
    a * c                              ∎
    where open SetoidReasoning Aˢ

  ∫-score : ∀ a f → ∫ (scoreP a) f ≈ a * (f ⟨$⟩ tt)
  ∫-score a f = weight-sum a (f ⟨$⟩ tt)

  scoreE : Hom S WQ (TQ (1Q S))
  scoreE = record
    { map = record
        { to = scoreP
        ; cong = λ e f → ∑-cong (λ r → *-cong (*-cong e refl) refl)
        }
    ; map-random = λ {α} _ → record
        { wα = const tt
        ; wα-random = tt
        ; wg = λ r k → (α ⟨$⟩ r) * dirac r₀ k
        ; wg-ok = λ _ → tt
        ; w-eq = λ r f → Setoid.refl Aˢ
        }
    }

  scaleP : ∀ {X : QBS S} → ∣A∣ → Pre X → Pre X
  scaleP c p = mk (α p) (α-random p) (λ r → c * μ p r) tt

  ∫-scale : ∀ {X : QBS S} (c : ∣A∣) (p : Pre X) f → ∫ (scaleP c p) f ≈ c * ∫ p f
  ∫-scale c p f = begin
    ∑ (λ r → (c * μ p r) * z r)    ≈⟨ ∑-cong (λ r → *-assoc c (μ p r) (z r)) ⟩
    ∑ (λ r → c * (μ p r * z r))    ≈⟨ ∑-scale c (λ r → μ p r * z r) ⟩
    c * ∑ (λ r → μ p r * z r)      ∎
    where open SetoidReasoning Aˢ
          z = λ r → f ⟨$⟩ α p r

  scaleE : ∀ {X : QBS S} → Hom S (1Q S) WQ → Hom S (1Q S) (TQ X) → Hom S (1Q S) (TQ X)
  scaleE a t = constE (scaleP (map a ⟨$⟩ tt) (map t ⟨$⟩ tt))

  -- countable sums of measures: glue the probes through the Cantor pairing
  sumP : ∀ {X : QBS S} → (ℕ → Pre X) → Pre X
  sumP {X} t = mk (λ k → α (t (lower (ιR k))) (ρR k))
    (random-cast X (λ _ → ≡.refl) (QBS.glue-random X {⇑ (λ k → lower (ιR k))} tt (λ n → ⇑ (α (t n)) ∘ₛ ⇑ ρR)
      (λ n → QBS.pre-random X (α-random (t n)) tt)))
    (λ k → μ (t (lower (ιR k))) (ρR k)) tt

  ∫-sum : ∀ {X : QBS S} (t : ℕ → Pre X) f →
    ∫ (sumP t) f ≈ ∑ (λ (n : R) → ∫ (t (lower n)) f)
  ∫-sum {X} t f = cantor (λ n m → μ (t (lower n)) m * (f ⟨$⟩ α (t (lower n)) m))

  sumE : ∀ {X : QBS S} → (ℕ → Hom S (1Q S) (TQ X)) → Hom S (1Q S) (TQ X)
  sumE ts = constE (sumP (λ n → map (ts n) ⟨$⟩ tt))

  -- countable sums of kernels: pointwise sums of measures, the witnesses glued through the pairing
  sumKH : ∀ {X Y : QBS S} → (ℕ → Hom S X (TQ Y)) → Hom S X (TQ Y)
  sumKH {X} {Y} ks = record
    { map = record
        { to = λ x → sumP (λ n → map (ks n) ⟨$⟩ x)
        ; cong = λ {x} {y} e f →
            Setoid.trans Aˢ (∫-sum (λ n → map (ks n) ⟨$⟩ x) f)
              (Setoid.trans Aˢ (∑-cong (λ n → Func.cong (map (ks (lower n))) e f))
                (Setoid.sym Aˢ (∫-sum (λ n → map (ks n) ⟨$⟩ y) f)))
        }
    ; map-random = λ {β} rβ →
        let w = λ n → map-random (ks n) rβ
            t′ = λ (r : R) (n : ℕ) → mk {Y} (MA.Wit.wα (w n)) (MA.Wit.wα-random (w n)) (MA.Wit.wg (w n) r) tt
        in record
          { wα = α (sumP (t′ r₀))
          ; wα-random = α-random (sumP (t′ r₀))
          ; wg = λ r → μ (sumP (t′ r))
          ; wg-ok = λ _ → tt
          ; w-eq = λ r f →
              Setoid.trans Aˢ (∫-sum (λ n → map (ks n) ⟨$⟩ (β ⟨$⟩ r)) f)
                (Setoid.trans Aˢ (∑-cong (λ n → MA.Wit.w-eq (w (lower n)) r f))
                  (Setoid.sym Aˢ (∫-sum (t′ r) f)))
          }
    }

  ----------------------------------------------------------------------------
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
  normP n p h = MP.mk (α p) (α-random p) (λ r → n * μ p r)
    (trans (∑-scale n (μ p)) (trans (*-comm n (mass p)) h))

  ∫-normP : ∀ {X : QBS S} n (p : Pre X) (h : mass p * n ≈ 1#) f →
    MP.∫ (normP n p h) f ≈ n * ∫ p f
  ∫-normP n p h f = ∫-scale n p f

  normC′ : ∀ {X : QBS S} (p : Pre X) → Σ ∣A∣ (λ n → mass p * n ≈ 1#) ⊎ (∀ n → mass p * n ≈ 1# → ⊥ {ℓ}) →
    ∣ MP.TQ X ∣ ⊎ ⊤ {ℓ}
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

  -- the decision on invertibility of a mass, as a value to case on
  InvDec : ∣A∣ → Set ℓ
  InvDec m = Σ ∣A∣ (λ n → m * n ≈ 1#) ⊎ (∀ n → m * n ≈ 1# → ⊥ {ℓ})

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
    massWg r = sym (mass-cong {X} {β r} {mk {X} wα wα-random (wg r) tt} (w-eq r))

    γ′ : ∀ r → InvDec (mass (β r)) → MP.Pre X
    γ′ r (inj₁ (n , h)) = normP n (β r) h
    γ′ r (inj₂ _) = MP.ηPre (wα r₀)

    wgγ′ : ∀ r → InvDec (mass (β r)) → R → ∣A∣
    wgγ′ r (inj₁ (n , _)) = λ k → n * wg r k
    wgγ′ r (inj₂ _) = dirac r₀

    wgγ-ok′ : ∀ r (e : InvDec (mass (β r))) → WeightClass.Ok (probClass A) (wgγ′ r e)
    wgγ-ok′ r (inj₁ (n , h)) = trans (∑-scale n (wg r))
                                 (trans (*-cong refl (massWg r)) (trans (*-comm n (mass (β r))) h))
    wgγ-ok′ r (inj₂ _) = WeightClass.ok-dirac (probClass A) r₀

    γ-eq′ : ∀ r (e : InvDec (mass (β r))) →
      MP._≈ᵖ_ (γ′ r e) (MP.mk {X} wα wα-random (wgγ′ r e) (wgγ-ok′ r e))
    γ-eq′ r (inj₁ (n , h)) f =
      Setoid.trans Aˢ (∫-normP n (β r) h f)
        (Setoid.trans Aˢ (*-cong refl (w-eq r f))
          (Setoid.sym Aˢ (∫-scale n (mk {X} wα wα-random (wg r) tt) f)))
    γ-eq′ r (inj₂ _) f =
      Setoid.trans Aˢ (MP.∫-η {X} (wα r₀) f) (Setoid.sym Aˢ (dirac-∑ r₀ (λ k → f ⟨$⟩ wα k)))

    Wγ : MP.Wit (λ r → γ′ r (d r))
    Wγ = record
      { wα = wα ; wα-random = wα-random
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

  module SA = Strength A (allClass A)

  -- the laws of the instance, stated in the notation of `StatisticalInterface`
  module Laws where
    open Category (QBSCat S) using () renaming (_≈_ to _≈ᵏ_; _∘_ to _∘ᵏ_; _⇒_ to _⇒ᵏ_)
    open Canonical.CartesianClosed (cartesianClosed S) using (!; ⟨_,_⟩) renaming (⊤ to 𝟙)
    open Cocartesian.BinaryCoproducts (Cocartesian.Cocartesian.coproducts (cocartesian S)) using (i₁; i₂)
    module M = Monad (CMS.StrongMonad.M SA.strongMonad)
    -- chains of equalities in the weights: transitivity and symmetry
    open Setoid Aˢ using () renaming (trans to infixr 5 _⟫_; sym to infix 8 ~_)

    zero-bind-law : ∀ (k : 𝟙 ⇒ᵏ M.F.F₀ 𝟙) → M.μ.η 𝟙 ∘ᵏ M.F.F₁ k ∘ᵏ constE zeroP ≈ᵏ constE zeroP
    zero-bind-law k pt f =
      ∫-join (mapPre k zeroP) f ⟫ ∑-zero _ (λ _ → zeroˡ _) ⟫ ~ ∫-zero f

    score-zero-law : scoreE ∘ᵏ constH 0# ≈ᵏ constE zeroP
    score-zero-law pt f = ∫-score 0# f ⟫ zeroˡ _ ⟫ ~ ∫-zero f

    score-mul-law : ∀ (a b : 𝟙 ⇒ᵏ WQ) → scoreE ∘ᵏ mulH ∘ᵏ ⟨ a , b ⟩ ≈ᵏ M.μ.η 𝟙 ∘ᵏ M.F.F₁ (scoreE ∘ᵏ b ∘ᵏ !) ∘ᵏ scoreE ∘ᵏ a
    score-mul-law a b pt f =
      let x = map a ⟨$⟩ pt
          y = map b ⟨$⟩ pt
          c = f ⟨$⟩ tt
          g = _∘H_ S scoreE (_∘H_ S b (!Q S))
      in ∫-score (x * y) f ⟫ *-assoc x y c ⟫ *-cong refl (~ ∫-score y f)
         ⟫ ~ weight-sum x (∫ (scoreP y) f) ⟫ ~ ∫-join (mapPre g (scoreP x)) f

    bind-sumK-law : ∀ {X Y} (ks : ℕ → X ⇒ᵏ M.F.F₀ Y) (t : 𝟙 ⇒ᵏ M.F.F₀ X) →
      M.μ.η Y ∘ᵏ M.F.F₁ (sumKH ks) ∘ᵏ t ≈ᵏ sumE (λ n → M.μ.η Y ∘ᵏ M.F.F₁ (ks n) ∘ᵏ t)
    bind-sumK-law {X} {Y} ks t pt f =
      let p = map t ⟨$⟩ pt
      in ∫-join (mapPre (sumKH ks) p) f
         ⟫ ∑-cong (λ r → *-cong (Setoid.refl Aˢ) (∫-sum (λ n → map (ks n) ⟨$⟩ α p r) f))
         ⟫ ∑-cong (λ r → ~ ∑-scale (μ p r) (λ n → ∫ (map (ks (lower n)) ⟨$⟩ α p r) f))
         ⟫ ∑-swap (λ r n → μ p r * ∫ (map (ks (lower n)) ⟨$⟩ α p r) f)
         ⟫ ~ (∫-sum (λ n → joinPre (mapPre (ks n) p)) f ⟫ ∑-cong (λ n → ∫-join (mapPre (ks (lower n)) p) f))

    score-one-law : scoreE ∘ᵏ constH 1# ≈ᵏ M.η.η 𝟙
    score-one-law pt f = ∫-score 1# f ⟫ *-identityˡ _ ⟫ ~ ∫-η {1Q S} pt f

    -- scaling a measure by a weight is a bind through `score`
    scale-def : ∀ {X} (a : 𝟙 ⇒ᵏ WQ) (t : 𝟙 ⇒ᵏ M.F.F₀ X) → scaleE a t ≈ᵏ M.μ.η X ∘ᵏ M.F.F₁ t ∘ᵏ scoreE ∘ᵏ a
    scale-def {X} a t pt f =
      ∫-scale {X} (map a ⟨$⟩ pt) (map t ⟨$⟩ pt) f
      ⟫ ~ (∫-join (mapPre t (scoreP (map a ⟨$⟩ pt))) f ⟫ ∫-score (map a ⟨$⟩ pt) (Comp.function (map t) (∫ᶠ f)))

    sum-join-law : ∀ {X} (ts : ℕ → 𝟙 ⇒ᵏ M.F.F₀ (M.F.F₀ X)) → M.μ.η X ∘ᵏ sumE ts ≈ᵏ sumE (λ n → M.μ.η X ∘ᵏ ts n)
    sum-join-law {X} ts pt f =
      let t = λ n → map (ts n) ⟨$⟩ tt
      in ∫-join (sumP t) f ⟫ ∫-sum t (∫ᶠ f) ⟫ ∑-cong (λ n → ~ ∫-join (t (lower n)) f) ⟫ ~ ∫-sum (λ n → joinPre (t n)) f

    normalize-prob-law : ∀ X → normH X ∘ᵏ Monad⇒-id.α.η inclusion X ≈ᵏ i₁
    normalize-prob-law X p = normProb p (NormalizableSemiring.invertible? N (mass (forgetPre p)))

    normalize-zero-law : ∀ {X} (x : 𝟙 ⇒ᵏ X) → normH X ∘ᵏ M.F.F₁ x ∘ᵏ constE zeroP ≈ᵏ i₂
    normalize-zero-law {X} x pt =
      normZero (mapPre x zeroP) (∑-zero _ (λ _ → refl))
      (NormalizableSemiring.invertible? N (mass (mapPre x zeroP)))

  open Laws

  discreteWeights : CommutativeMonoidWithZero (QBSCat S) (cartesianClosed S)
  discreteWeights = record
    { W = WQ
    ; mulW = mulH
    ; oneW = constH 1#
    ; zero⇒ = constH 0#
    ; mul-assoc = λ a b c z → *-assoc _ _ _
    ; mul-comm = λ a b z → *-comm _ _
    ; mul-one = λ a z → *-identityʳ _
    ; mul-zero = λ a z → zeroʳ _
    }

  discreteMeasures : SubMonad (discreteProb A)
  discreteMeasures = record
    { commutativeMonad = record { strongMonad = SA.strongMonad ; commutative = SA.commutative }
    ; inclusion = inclusion
    ; inclusion-strong = λ _ _ _ _ → Setoid.refl Aˢ
    }

  discreteScore : Score discreteWeights discreteMeasures
  discreteScore = record
    { zero = constE zeroP
    ; zero-bind = zero-bind-law
    ; score = scoreE
    ; score-zero = score-zero-law
    ; score-one = score-one-law
    ; score-mul = score-mul-law
    }

  discreteSums : CountableSums discreteMeasures
  discreteSums = record
    { sumK = sumKH
    ; sumK-point = λ ks x pt f → Setoid.refl Aˢ
    ; bind-sumK = bind-sumK-law
    ; sum-nat = λ {X} {Y} f ts pt g →
        Setoid.trans Aˢ (∫-sum (λ n → map (ts n) ⟨$⟩ tt) (Comp.function (map f) g))
          (Setoid.sym Aˢ (∫-sum (λ n → mapPre f (map (ts n) ⟨$⟩ tt)) g))
    ; sum-join = sum-join-law
    }

  module DS′ = Score discreteScore
  module DM′ = CountableSums discreteSums

  -- the laws involving the derived `scaleM`, bridged to the direct `scaleE` by `scale-def`
  module Laws₂ where
    open Category (QBSCat S) using () renaming (_≈_ to _≈ᵏ_; _∘_ to _∘ᵏ_; _⇒_ to _⇒ᵏ_)
    open Canonical.CartesianClosed (cartesianClosed S) using (!; ⟨_,_⟩) renaming (⊤ to 𝟙)
    open Setoid Aˢ using () renaming (trans to infixr 5 _⟫_; sym to infix 8 ~_)

    scaled-laws-law : ∀ {X} (t : 𝟙 ⇒ᵏ M.F.F₀ X) →
      Σ (ℕ → ℛQ S ⇒ᵏ X) λ a → Σ (ℕ → 𝟙 ⇒ᵏ WQ) λ w → Σ (ℕ → ProbabilityInterface.Measure (discreteProb A)) λ μ →
        t ≈ᵏ DM′.sumM
            (λ n → DS′.scaleM (w n) (Monad⇒-id.α.η inclusion X ∘ᵏ ProbabilityInterface.law (discreteProb A) (a n) (μ n)))
    -- a countable sum of global measures is, pointwise in the integrals, the sum of the pre-measures
    sumM-∫ : ∀ {X} (D : ℕ → 𝟙 ⇒ᵏ M.F.F₀ X) (fam : ℕ → Pre X) →
      (∀ n f → ∫ (map (D n) ⟨$⟩ tt) f ≈ ∫ (fam n) f) → ∀ f → ∫ (map (DM′.sumM D) ⟨$⟩ tt) f ≈ ∫ (sumP fam) f
    sumM-∫ D fam h f = ∫-sum (λ n → map (D n) ⟨$⟩ tt) f ⟫ ∑-cong (λ n → h (lower n) f) ⟫ ~ ∫-sum fam f

    scaled-laws-law {X} t =
      let p = map t ⟨$⟩ tt
          lawA = λ (n : ℕ) → mk {X} (λ r → α p r) (α-random p) (dirac (lift n)) tt
          fam = λ (n : ℕ) → scaleP (μ p (lift n)) (lawA n)
          aN = λ (n : ℕ) → probe S (α-random p)
          wN = λ (n : ℕ) → constH (μ p (lift n))
          μN = λ (n : ℕ) → dirac (lift n) , WeightClass.ok-dirac (probClass A) (lift n)
          D = λ (n : ℕ) → DS′.scaleM (wN n) (Monad⇒-id.α.η inclusion X ∘ᵏ ProbabilityInterface.law (discreteProb A) (aN n) (μN n))
      in aN , wN , μN
       , (λ pt f → ~
           (sumM-∫ D fam
           (λ n f′ → ~ scale-def (wN n)
           (Monad⇒-id.α.η inclusion X ∘ᵏ ProbabilityInterface.law (discreteProb A) (aN n) (μN n)) tt f′) f
                      ⟫ ∫-sum fam f ⟫ ∑-cong (λ n → ∫-scale (μ p n) (lawA (lower n)) f
                                       ⟫ *-cong refl (dirac-∑ n (λ k → f ⟨$⟩ α p k)))))

    normalize-scale-law : ∀ {X} (a b : 𝟙 ⇒ᵏ WQ) → mulH ∘ᵏ ⟨ a , b ⟩ ≈ᵏ constH 1# →
      ∀ (t : 𝟙 ⇒ᵏ M.F.F₀ X) → normH X ∘ᵏ DS′.scaleM a t ≈ᵏ normH X ∘ᵏ t
    normalize-scale-law {X} a b hab t pt =
      Setoid.trans (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S)))
        (Func.cong (map (normH X)) (λ f → ~ scale-def a t pt f))
        (normScale (map a ⟨$⟩ pt) (map b ⟨$⟩ pt) (hab pt) (map t ⟨$⟩ pt)
          (NormalizableSemiring.invertible? N (mass (scaleP (map a ⟨$⟩ pt) (map t ⟨$⟩ pt))))
          (NormalizableSemiring.invertible? N (mass (map t ⟨$⟩ pt))))

  open Laws₂

  discreteStat : StatisticalInterface ℓ (QBSCat S) (ℛQ S) (cartesianClosed S) (discreteProb A)
    (Cocartesian.Cocartesian.coproducts (cocartesian S))
  discreteStat = record
    { weights = discreteWeights
    ; measures = discreteMeasures
    ; scoring = discreteScore
    ; sums = discreteSums
    ; scaled-laws = scaled-laws-law
    ; normalization = record
        { normalize = normH
        ; normalize-prob = normalize-prob-law
        ; normalize-zero = normalize-zero-law
        ; normalize-scale = normalize-scale-law
        }
    }
