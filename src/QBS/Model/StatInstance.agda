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
    S = discreteSource ℓ
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
    ; Random = λ _ → ⊤
    ; random-resp = λ _ _ → tt
    ; const-random = λ _ → tt
    ; pre-random = λ _ _ → tt
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

  open MA using (Pre; mk; ∫; ∫ᶠ; mapPre; ηPre; joinPre; ∫-η; ∫-join; TQ; TH; TM; TF)
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
        ; wg = λ r k → α r * dirac r₀ k
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
    (QBS.glue-random X {λ k → lower (ιR k)} tt (λ n → α (t n) ∘ ρR)
      (λ n → QBS.pre-random X (α-random (t n)) tt))
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
              Setoid.trans Aˢ (∫-sum (λ n → map (ks n) ⟨$⟩ (β r)) f)
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
    normRandomᵈ : QBS.Random (_+Q_ S (MP.TQ X) (1Q S)) (λ r → normC′ (β r) (d r))
    normRandomᵈ = idxᵈ , tt , c , eq
      where
        c : ℕ → Piece S (MP.TQ X) (1Q S)
        c ℕ.zero = inj₁ ((λ r → γ′ r (d r)) , Wγ)
        c (ℕ.suc _) = inj₂ ((λ _ → tt) , tt)

        eq : ∀ r → Setoid._≈_ (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S)))
               (normC′ (β r) (d r)) (ev S (MP.TQ X) (1Q S) (c (idxᵈ r)) r)
        eq r with d r in ed
        ... | inj₁ (n , h) rewrite ed = ⊎ʳ.inj₁ (λ f → Setoid.refl Aˢ)
        ... | inj₂ _ rewrite ed = ⊎ʳ.inj₂ ≡.refl

  normRandom : ∀ {X : QBS S} {β : R → Pre X} → MA.Wit β →
    QBS.Random (_+Q_ S (MP.TQ X) (1Q S)) (λ r → normC (β r))
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

  discreteStat : StatisticalInterface ℓ (QBSCat S) (ℛQ S) (cartesianClosed S) (discreteProb A)
    (Cocartesian.Cocartesian.coproducts (cocartesian S))
  discreteStat = record
    { W = WQ
    ; mulW = mulH
    ; oneW = constH 1#
    ; zeroW = constH 0#
    ; mul-assoc = λ a b c z → *-assoc _ _ _
    ; mul-comm = λ a b z → *-comm _ _
    ; mul-one = λ a z → *-identityʳ _
    ; mul-zero = λ a z → zeroʳ _
    ; commutativeMonad = record { strongMonad = SA.strongMonad ; commutative = SA.commutative }
    ; inclusion = inclusion
    ; inclusion-strong = λ _ _ _ _ → Setoid.refl Aˢ
    ; zero = constE zeroP
    ; zero-bind = λ k pt f →
        Setoid.trans Aˢ (∫-join (mapPre k zeroP) f)
          (Setoid.trans Aˢ (∑-zero _ (λ _ → zeroˡ _)) (Setoid.sym Aˢ (∫-zero f)))
    ; score = scoreE
    ; score-zero = λ pt f → Setoid.trans Aˢ (∫-score 0# f) (Setoid.trans Aˢ (zeroˡ _) (Setoid.sym Aˢ (∫-zero f)))
    ; score-mul = λ a b pt f →
        let x = map a ⟨$⟩ pt
            y = map b ⟨$⟩ pt
            c = f ⟨$⟩ tt
            g = _∘H_ S scoreE (_∘H_ S b (!Q S))
        in Setoid.trans Aˢ (∫-score (x * y) f)
             (Setoid.trans Aˢ (*-assoc x y c)
               (Setoid.trans Aˢ (*-cong refl (Setoid.sym Aˢ (∫-score y f)))
                 (Setoid.trans Aˢ (Setoid.sym Aˢ (weight-sum x (∫ (scoreP y) f)))
                   (Setoid.sym Aˢ (∫-join (mapPre g (scoreP x)) f)))))
    ; sumM = sumE
    ; scaleM = scaleE
    ; sumK = sumKH
    ; sumK-point = λ ks x pt f → Setoid.refl Aˢ
    ; bind-sumK = λ {X} {Y} ks t pt f →
        let p = map t ⟨$⟩ pt
        in Setoid.trans Aˢ (∫-join (mapPre (sumKH ks) p) f)
             (Setoid.trans Aˢ (∑-cong (λ r → *-cong (Setoid.refl Aˢ) (∫-sum (λ n → map (ks n) ⟨$⟩ α p r) f)))
               (Setoid.trans Aˢ (∑-cong (λ r → Setoid.sym Aˢ (∑-scale (μ p r) (λ n → ∫ (map (ks (lower n)) ⟨$⟩ α p r) f))))
                 (Setoid.trans Aˢ (∑-swap (λ r n → μ p r * ∫ (map (ks (lower n)) ⟨$⟩ α p r) f))
                   (Setoid.sym Aˢ (Setoid.trans Aˢ (∫-sum (λ n → joinPre (mapPre (ks n) p)) f)
                     (∑-cong (λ n → ∫-join (mapPre (ks (lower n)) p) f)))))))
    ; scale-one = λ {X} t pt f → Setoid.trans Aˢ (∫-scale {X} 1# (map t ⟨$⟩ pt) f) (*-identityˡ _)
    ; scale-mul = λ {X} a b t pt f →
        let xa = map a ⟨$⟩ pt
            xb = map b ⟨$⟩ pt
            p = map t ⟨$⟩ pt
        in Setoid.trans Aˢ (∫-scale {X} (xa * xb) p f)
             (Setoid.trans Aˢ (*-assoc xa xb (∫ p f))
               (Setoid.trans Aˢ (*-cong refl (Setoid.sym Aˢ (∫-scale {X} xb p f)))
                 (Setoid.sym Aˢ (∫-scale {X} xa (scaleP xb p) f))))
    ; scale-return = λ a x pt f → Setoid.refl Aˢ
    ; scale-sum = λ {X} a ts pt f →
        let c = map a ⟨$⟩ pt
            t = λ n → map (ts n) ⟨$⟩ tt
        in Setoid.trans Aˢ (∫-scale {X} c (sumP t) f)
             (Setoid.trans Aˢ (*-cong refl (∫-sum t f))
               (Setoid.trans Aˢ (Setoid.sym Aˢ (∑-scale c (λ n → ∫ (t (lower n)) f)))
                 (Setoid.trans Aˢ (∑-cong (λ n → Setoid.sym Aˢ (∫-scale {X} c (t (lower n)) f)))
                   (Setoid.sym Aˢ (∫-sum (λ n → scaleP c (t n)) f)))))
    ; sum-nat = λ {X} {Y} f ts pt g →
        Setoid.trans Aˢ (∫-sum (λ n → map (ts n) ⟨$⟩ tt) (Comp.function (map f) g))
          (Setoid.sym Aˢ (∫-sum (λ n → mapPre f (map (ts n) ⟨$⟩ tt)) g))
    ; sum-join = λ {X} ts pt f →
        let t = λ n → map (ts n) ⟨$⟩ tt
        in Setoid.trans Aˢ (∫-join (sumP t) f)
             (Setoid.trans Aˢ (∫-sum t (∫ᶠ f))
               (Setoid.trans Aˢ (∑-cong (λ n → Setoid.sym Aˢ (∫-join (t (lower n)) f)))
                 (Setoid.sym Aˢ (∫-sum (λ n → joinPre (t n)) f))))
    ; scale-nat = λ f a t pt g → Setoid.refl Aˢ
    ; scale-join = λ {X} a t pt f →
        let c = map a ⟨$⟩ pt
            p = map t ⟨$⟩ pt
        in Setoid.trans Aˢ (∫-join (scaleP c p) f)
             (Setoid.trans Aˢ (∫-scale c p (∫ᶠ f))
               (Setoid.trans Aˢ (*-cong refl (Setoid.sym Aˢ (∫-join p f)))
                 (Setoid.sym Aˢ (∫-scale c (joinPre p) f))))
    ; scaled-laws = λ {X} t →
        let p = map t ⟨$⟩ tt
            lawA = λ (n : ℕ) → mk {X} (λ r → α p r) (QBS.pre-random X {α p} {id} (α-random p) tt) (dirac (lift n)) tt
            fam = λ (n : ℕ) → scaleP (μ p (lift n)) (lawA n)
        in (λ n → probe S (α-random p))
         , (λ n → constH (μ p (lift n)))
         , (λ n → dirac (lift n) , WeightClass.ok-dirac (probClass A) (lift n))
         , (λ pt f → Setoid.sym Aˢ (Setoid.trans Aˢ (∫-sum fam f)
             (∑-cong (λ n → Setoid.trans Aˢ (∫-scale (μ p n) (lawA (lower n)) f)
               (*-cong refl (dirac-∑ n (λ k → f ⟨$⟩ α p k)))))))
    ; normalize = normH
    ; normalize-prob = λ X p → normProb p (NormalizableSemiring.invertible? N (mass (forgetPre p)))
    ; normalize-zero = λ {X} x pt → normZero (mapPre x zeroP) (∑-zero _ (λ _ → refl))
        (NormalizableSemiring.invertible? N (mass (mapPre x zeroP)))
    ; normalize-scale = λ {X} a b hab t pt →
        normScale (map a ⟨$⟩ pt) (map b ⟨$⟩ pt) (hab pt) (map t ⟨$⟩ pt)
          (NormalizableSemiring.invertible? N (mass (scaleP (map a ⟨$⟩ pt) (map t ⟨$⟩ pt))))
          (NormalizableSemiring.invertible? N (mass (map t ⟨$⟩ pt)))
    }
