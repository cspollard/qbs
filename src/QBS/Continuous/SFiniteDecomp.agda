{-# OPTIONS --safe --without-K #-}

-- SKELETON (holes).  Every s-finite measure is a countable sum of scaled laws of probability
-- measures: the `scaled-laws` field of `StatisticalInterface`.
--
-- A measure `[α, m, w]` is split along the level sets `Bₙ = {r | n ≤ w r < n+1}` of its weight.
-- On `Bₙ` the density `dₙ = (min(w, n+1)·χ_{Bₙ}) / (n+1)` is `Meas` and `≤ 1`, so `ν ₙ = dₙ · m` is a
-- sub-probability measure of mass `cₙ`; classically either `cₙ` is invertible (then `μₙ = cₙ⁻¹ νₙ`
-- is a probability measure) or `cₙ ≈ 0` (then any `μₙ` works with weight 0).  The scaled constant is
-- `(n+1)·cₙ`, and the probe is `x ∘ α`.

-- Prob is a sub-monad of the s-finite measures (`inclusion`: weight 1), the zero measure and `score`.

module QBS.Continuous.SFiniteDecomp where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ; !Q)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (R₁; cantorSource; down)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad using (module Continuous)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteMonad using (module SFiniteMonad)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.ProbInstance using (module ContinuousProb)
open import QBS.Statistical using (StatisticalInterface)
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (cocartesian; _+Q_; Piece; ev)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.JSum using (module JSum)
import Data.Nat.Base as ℕ
open import QBS.Continuous.Strong using (module Strength)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import QBS.Analysis.Density using (module Density)
open import QBS.Analysis.LevelSets using (module LevelSets)
import QBS.Analysis.RationalLemmas as RL
import Data.Rational.Unnormalised.Base as ℚ
open import QBS.Analysis.LowerReals using (oneC; zeroC; infC; _⊑_; mk⊑; ⊗-mono; ⊑-refl; ⊑-trans)
open import QBS.Analysis.LowerRealsArch using (qC; nat-nonneg)
open import QBS.Analysis.LowerInverse using (invC; inv-mul-⊑; module InvClassical)
open import QBS.Borel.Core using (Borel; inter₂; union₂; compl)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Nat.Properties as ℕP
import Data.Unit.Base as U1
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Empty using (⊥-elim)
open Cut renaming (mem to memC; down to downC; open′ to openC; neg to negC)

module SFiniteDecomp (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zeroW)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open Density lem using (densM; J-dens; J-null; Mvh)
  open LevelSets lem using (LS; Lvl; borel-prop)
  open Split funext
  open UnitInterval A using (AQ)
  open RandomSource S using () renaming (meas-id to measId)
  open SFinite lem funext
  open WitM
  open SFiniteMonad lem funext
  open SFiniteStrong lem funext
  open SFiniteSum lem funext
  open SFiniteIncl lem funext
  open Series A
  open JSum lem using (J-∑; Meas-∑)
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- 1. measures with a `Meas` density (sub-probability when the density is ≤ 1)

  densityBd : ∀ (m : Measure) (d : R₁ → Cut) (md : Meas d) (d≤1 : ∀ r → d r ≤ 1#) → 1# * J m d md ≤ 1#
  densityBd m d md d≤1 =
    ≤-trans (≤-reflexive (*-identityˡ _))
     (≤-trans (J-mono m md (LS (Fun-const 1# ≤-refl)) d≤1)
      (≤-trans (≤-reflexive (J-fun m (Fun-const 1# ≤-refl)))
       (Measure.I-sub m (Fun-const 1# ≤-refl))))

  densityM : ∀ (m : Measure) (d : R₁ → Cut) → Meas d → (∀ r → d r ≤ 1#) → Measure
  densityM m d md d≤1 = densM m d md 1# (densityBd m d md d≤1)

  I-densityM : ∀ (m : Measure) (d : R₁ → Cut) (md : Meas d) (d≤1 : ∀ r → d r ≤ 1#) →
    ∀ h (fh : Fun h) (mdh : Meas (λ r → d r * h r)) →
    Measure.I (densityM m d md d≤1) h fh ≈ J m (λ r → d r * h r) mdh
  I-densityM m d md d≤1 h fh mdh = trans (*-identityˡ _)
    (J-cong m (Mvh {d} {h} md fh) mdh (λ r → refl))

  -- the total mass of a (sub-probability) measure
  massM : Measure → Cut
  massM ν = Measure.I ν (const 1#) (Fun-const 1# ≤-refl)

  -- normalisation of a measure of invertible mass (classical inverse, `Analysis/LowerInverse`)
  Jmass : ∀ (ν : Measure) → J ν (const 1#) (Meas-const 1#) ≈ massM ν
  Jmass ν = trans (J-irrel ν (Meas-const 1#) (LS (Fun-const 1# ≤-refl))) (J-fun ν (Fun-const 1# ≤-refl))

  normBd : ∀ (ν : Measure) (n : Cut) → massM ν * n ≈ 1# → n * J ν (const 1#) (Meas-const 1#) ≤ 1#
  normBd ν n h = ≤-reflexive (trans (*-cong refl (Jmass ν)) (trans (*-comm _ _) h))

  normD : ∀ (ν : Measure) (n : Cut) → massM ν * n ≈ 1# → Measure
  normD ν n h = densM ν (const 1#) (Meas-const 1#) n (normBd ν n h)

  I-normD : ∀ (ν : Measure) (n : Cut) (h : massM ν * n ≈ 1#) f (ff : Fun f) →
    Measure.I (normD ν n h) f ff ≈ n * Measure.I ν f ff
  I-normD ν n h f ff = *-cong refl
    (trans (J-cong ν (Mvh {const 1#} {f} (Meas-const 1#) ff) (LS ff) (λ r → *-identityˡ (f r))) (J-fun ν ff))

  normD-prob : ∀ (ν : Measure) (n : Cut) (h : massM ν * n ≈ 1#) → IsProb (normD ν n h)
  normD-prob ν n h = trans (I-normD ν n h (const 1#) (Fun-const 1# ≤-refl)) (trans (*-comm _ _) h)

  normM : ∀ (ν : Measure) (n : Cut) → massM ν * n ≈ 1# → Σ Measure IsProb
  normM ν n h = normD ν n h , normD-prob ν n h

  I-normM : ∀ (ν : Measure) (n : Cut) (h : massM ν * n ≈ 1#) f (ff : Fun f) →
    Measure.I (proj₁ (normM ν n h)) f ff ≈ n * Measure.I ν f ff
  I-normM ν n h f ff = I-normD ν n h f ff

  ----------------------------------------------------------------------------
  -- 2. the level-set pieces of a measure `[α, m, w]`

  -- the cut `P ∧ c`: `c` if `P` holds and `0` otherwise
  chi : Set → Cut → Cut
  chi P c = record
    { mem = λ q → q ℚ.< RL.0Q ⊎ (P × memC c q)
    ; down = λ { le (inj₁ lt) → inj₁ (RL.≤-<-trans le lt) ; le (inj₂ (pp , m)) → inj₂ (pp , downC c le m) }
    ; open′ = λ { (inj₁ lt) → let r , q<r , r<0 = RL.dense lt in r , q<r , inj₁ r<0
                ; (inj₂ (pp , m)) → let r , q<r , mr = openC c m in r , q<r , inj₂ (pp , mr) }
    ; neg = inj₁ }

  chi-true : ∀ {P} c → P → chi P c ≈ c
  chi-true c pp = mk⊑ (λ q → λ { (inj₁ lt) → negC c lt ; (inj₂ (_ , m)) → m }) , mk⊑ (λ q m → inj₂ (pp , m))

  chi-false : ∀ {P} c → (P → ⊥) → chi P c ≈ 0#
  chi-false c np = mk⊑ (λ q → λ { (inj₁ lt) → lt ; (inj₂ (pp , _)) → ⊥-elim (np pp) }) , mk⊑ (λ q lt → inj₁ lt)

  Meas-chi : ∀ {U : R₁ → Set} {g} → Borel (λ c → U (lift c)) → Meas g → Meas (λ x → chi (U x) (g x))
  Meas-chi bU mg q = union₂ (borel-prop (q ℚ.< RL.0Q)) (inter₂ bU (mg q))

  -- the weight of a pre-measure
  wt : ∀ {X : QBS S} → Pre (XW X) → R₁ → Cut
  wt p r = proj₁ (α p r)

  wt-Meas : ∀ {X : QBS S} (p : Pre (XW X)) → Meas (wt p)
  wt-Meas p = proj₁ (α-random p)

  -- the bands: index 0 is `{w = ∞}` (weight ∞), index k+1 is `{k < w ≤ k+1}` (weight k+1)
  posNat : ∀ k → RL.0Q ℚ.< RL.nat (ℕ.suc k)
  posNat k = RL.≃-<ʳ (RL.≃-sym (RL.nat-suc k))
    (RL.<-≤-trans RL.0<1 (RL.≤-trans (RL.≤-≃ (RL.≃-sym (RL.+-identityˡ RL.1Q)))
       (RL.+-mono-≤ (nat-nonneg k) (RL.≤-refl {RL.1Q}))))

  cK : ℕ → Cut
  cK k = qC (RL.nat (ℕ.suc k)) (posNat k)

  bandW : ℕ → Cut
  bandW ℕ.zero = infC
  bandW (ℕ.suc k) = cK k

  infS : Cut → Set
  infS w = ∀ q → memC w q

  bandS : Cut → ℕ → Set
  bandS w k = memC w (RL.nat k) × (memC w (RL.nat (ℕ.suc k)) → ⊥)

  -- Bₙ as a weight function: the (rescaled) weight on the band, `0` elsewhere
  densW : Cut → ℕ → Cut
  densW w ℕ.zero = chi (infS w) 1#
  densW w (ℕ.suc k) = chi (bandS w k) (invC (cK k) * w)

  pieceDensity : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → R₁ → Cut
  pieceDensity p n r = densW (wt p r) n

  pieceDensity-Meas : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Meas (pieceDensity p n)
  pieceDensity-Meas p ℕ.zero = Meas-chi {λ x → infS (wt p x)} {λ _ → 1#} (all-enum (λ ρ c → Lvl (wt p) ρ c) (wt-Meas p)) (Meas-const 1#)
  pieceDensity-Meas p (ℕ.suc k) = Meas-chi {λ x → bandS (wt p x) k} {λ x → invC (cK k) * wt p x}
    (inter₂ (wt-Meas p (RL.nat k)) (compl (wt-Meas p (RL.nat (ℕ.suc k)))))
    (Meas-⊗ {λ _ → invC (cK k)} {wt p} (Meas-const (invC (cK k))) (wt-Meas p))

  -- on a band, `w ≤ k+1`, so `(k+1)⁻¹ w ≤ 1`
  band⊑ : ∀ w k → bandS w k → w ⊑ cK k
  band⊑ w k (_ , nm) = mk⊑ (λ q m → go q m (RL.≤-or-> (RL.nat (ℕ.suc k)) q))
    where
      go : ∀ q → memC w q → RL.nat (ℕ.suc k) ℚ.≤ q ⊎ q ℚ.< RL.nat (ℕ.suc k) → q ℚ.< RL.nat (ℕ.suc k)
      go q m (inj₁ le) = ⊥-elim (nm (downC w le m))
      go q m (inj₂ lt) = lt

  band-inv≤1 : ∀ w k → bandS w k → invC (cK k) * w ≤ 1#
  band-inv≤1 w k b = ⊑-trans (⊗-mono ⊑-refl (band⊑ w k b)) (inv-mul-⊑ (cK k))

  densW≤1 : ∀ w n → densW w n ≤ 1#
  densW≤1 w ℕ.zero = mk⊑ (λ q → λ { (inj₁ lt) → RL.<-trans lt RL.0<1 ; (inj₂ (_ , m)) → m })
  densW≤1 w (ℕ.suc k) = mk⊑ (λ q → λ { (inj₁ lt) → RL.<-trans lt RL.0<1
                                       ; (inj₂ (b , m)) → _⊑_.ap (band-inv≤1 w k b) q m })

  pieceDensity≤1 : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) r → pieceDensity p n r ≤ 1#
  pieceDensity≤1 p n r = densW≤1 (wt p r) n

  -- the bands are monotone in the index and disjoint
  nat-mono : ∀ {j k} → j ℕ.≤ k → RL.nat j ℚ.≤ RL.nat k
  nat-mono {k = k} ℕ.z≤n = nat-nonneg k
  nat-mono (ℕ.s≤s le) = RL.≤-resp (RL.≃-sym (RL.nat-suc _)) (RL.≃-sym (RL.nat-suc _))
    (RL.+-mono-≤ (nat-mono le) (RL.≤-refl {RL.1Q}))

  band-unique : ∀ w {j k} → bandS w j → bandS w k → j ≡.≡ k
  band-unique w {j} {k} (mj , nj) (mk′ , nk) with ℕP.<-cmp j k
  ... | tri< lt _ _ = ⊥-elim (nj (downC w (nat-mono lt) mk′))
  ... | tri≈ _ e _ = e
  ... | tri> _ _ gt = ⊥-elim (nk (downC w (nat-mono gt) mj))

  band-ninf : ∀ w k → bandS w k → infS w → ⊥
  band-ninf w k (_ , nm) inf = nm (inf _)

  -- a bounded search for the band of a finite positive weight
  find-band : ∀ w K → memC w (RL.nat 0) → (memC w (RL.nat K) → ⊥) → Σ ℕ (bandS w)
  find-band w ℕ.zero m0 nK = ⊥-elim (nK m0)
  find-band w (ℕ.suc K) m0 nK with lem (memC w (RL.nat K))
  ... | inj₁ mK = K , mK , nK
  ... | inj₂ nmK = find-band w K m0 nmK

  bands-case : ∀ w → infS w ⊎ ((memC w RL.0Q → ⊥) ⊎ Σ ℕ (bandS w))
  bands-case w with lem (infS w)
  ... | inj₁ inf = inj₁ inf
  ... | inj₂ ninf with lem (memC w RL.0Q)
  ... | inj₂ nz = inj₂ (inj₁ nz)
  ... | inj₁ m0 with lem (Σ RL.Q (λ ρ → memC w ρ → ⊥))
  ... | inj₁ (ρ , nρ) = inj₂ (inj₂ (find-band w (proj₁ (RL.nat-bound ρ)) m0
        (λ m → nρ (downC w (proj₂ (RL.nat-bound ρ)) m))))
  ... | inj₂ nex = ⊥-elim (ninf (λ q → dec q (lem (memC w q))))
    where dec : ∀ q → memC w q ⊎ (memC w q → ⊥) → memC w q
          dec q (inj₁ m) = m
          dec q (inj₂ nq) = ⊥-elim (nex (q , nq))

  cK-inv : ∀ k w → cK k * (invC (cK k) * w) ≈ w
  cK-inv k w = trans (sym (*-assoc _ _ _))
    (trans (*-cong (*-comm _ _) refl) (trans (*-cong (inv-mul′ k) refl) (*-identityˡ w)))
    where
      inv-mul′ : ∀ k → invC (cK k) * cK k ≈ 1#
      inv-mul′ k = InvClassical.inv-mul lem (cK k)
        (proj₁ (RL.dense (posNat k)) , proj₁ (proj₂ (RL.dense (posNat k))) , proj₂ (proj₂ (RL.dense (posNat k))))
        (RL.nat (ℕ.suc k) , RL.<-irrefl RL.≃-refl)

  -- the weight is the sum of the pieces: w · c ≈ Σₙ (weightₙ · dₙ) · c
  bandTerm : Cut → Cut → ℕ → Cut
  bandTerm w c n = (bandW n * densW w n) * c

  bands-zero : ∀ w c → (memC w RL.0Q → ⊥) → w * c ≈ ∑ᶠ (bandTerm w c)
  bands-zero w c nz = trans w0 (sym (∑ᶠ-zero t0))
    where
      w0 : w * c ≈ 0#
      w0 = trans (*-cong ((mk⊑ (λ q m → go q m (RL.≤-or-> RL.0Q q))) , mk⊑ (λ q lt → negC w lt)) refl) (zeroˡ c)
        where go : ∀ q → memC w q → RL.0Q ℚ.≤ q ⊎ q ℚ.< RL.0Q → q ℚ.< RL.0Q
              go q m (inj₁ le) = ⊥-elim (nz (downC w le m))
              go q m (inj₂ lt) = lt
      d0 : ∀ n → densW w n ≈ 0#
      d0 ℕ.zero = chi-false _ (λ inf → nz (inf RL.0Q))
      d0 (ℕ.suc k) = chi-false _ (λ b → nz (downC w (nat-nonneg k) (proj₁ b)))
      t0 : ∀ n → bandTerm w c n ≈ 0#
      t0 n = trans (*-cong (trans (*-cong refl (d0 n)) (zeroʳ _)) refl) (zeroˡ c)

  bands-inf : ∀ w c → infS w → w * c ≈ ∑ᶠ (bandTerm w c)
  bands-inf w c inf = trans (*-cong wi refl) (trans (*-cong (sym (*-identityʳ _)) refl)
    (trans (*-cong (*-cong refl (sym (chi-true 1# inf))) refl) (sym (∑ᶠ-single ℕ.zero other))))
    where
      wi : w ≈ infC
      wi = mk⊑ (λ q _ → U1.tt) , mk⊑ (λ q _ → inf q)
      other : ∀ n → (n ≡.≡ ℕ.zero → ⊥) → bandTerm w c n ≈ 0#
      other ℕ.zero ne = ⊥-elim (ne ≡.refl)
      other (ℕ.suc k) ne = trans (*-cong (trans (*-cong refl (chi-false _ (λ b → band-ninf w k b inf))) (zeroʳ _)) refl) (zeroˡ c)

  bands-band : ∀ w c k → bandS w k → w * c ≈ ∑ᶠ (bandTerm w c)
  bands-band w c k b = trans (*-cong (sym (cK-inv k w)) refl)
    (trans (*-cong (*-cong refl (sym (chi-true _ b))) refl) (sym (∑ᶠ-single (ℕ.suc k) other)))
    where
      other : ∀ n → (n ≡.≡ ℕ.suc k → ⊥) → bandTerm w c n ≈ 0#
      other ℕ.zero ne = trans (*-cong (trans (*-cong refl (chi-false _ (band-ninf w k b))) (zeroʳ _)) refl) (zeroˡ c)
      other (ℕ.suc j) ne = trans (*-cong (trans (*-cong refl (chi-false _ (λ bj → ne (≡.cong ℕ.suc (band-unique w bj b))))) (zeroʳ _)) refl) (zeroˡ c)

  bands-sum : ∀ w c → w * c ≈ ∑ᶠ (bandTerm w c)
  bands-sum w c with bands-case w
  ... | inj₁ inf = bands-inf w c inf
  ... | inj₂ (inj₁ nz) = bands-zero w c nz
  ... | inj₂ (inj₂ (k , b)) = bands-band w c k b

  pieces-sum : ∀ {X : QBS S} (p : Pre (XW X)) r (c : Cut) →
    wt p r * c ≈ ∑ᶠ (λ n → (bandW n * pieceDensity p n r) * c)
  pieces-sum p r c = bands-sum (wt p r) c

  pieceMeasure : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Measure
  pieceMeasure p n = densityM (m p) (pieceDensity p n) (pieceDensity-Meas p n) (pieceDensity≤1 p n)

  -- the integrand of the n-th piece against a test function f
  pieceψ : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) (f : Hom S X WQ) → R₁ → Cut
  pieceψ {X} p n f r = pieceDensity p n r * (map f ⟨$⟩ proj₂ (α p r))

  pieceψ-Meas : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) (f : Hom S X WQ) → Meas (pieceψ {X} p n f)
  pieceψ-Meas {X} p n f = Meas-⊗ {pieceDensity p n} {λ r → map f ⟨$⟩ proj₂ (α p r)} (pieceDensity-Meas p n) (map-random f (proj₂ (α-random p)))

  -- the weighted n-th piece
  pieceTerm : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) (n : ℕ) → R₁ → Cut
  pieceTerm {X} p f n r = bandW n * pieceψ {X} p n f r

  pieceTerm-Meas : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) (n : ℕ) → Meas (pieceTerm {X} p f n)
  pieceTerm-Meas {X} p f n = Meas-⊗ {λ _ → bandW n} {pieceψ {X} p n f} (Meas-const (bandW n)) (pieceψ-Meas {X} p n f)

  ψ-pieces : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) r →
    ψ {X} p f r ≈ ∑ᶠ (λ n → pieceTerm {X} p f n r)
  ψ-pieces {X} p f r = trans (pieces-sum p r (map f ⟨$⟩ proj₂ (α p r)))
    (∑ᶠ-cong (λ n → *-assoc (bandW n) (pieceDensity p n r) (map f ⟨$⟩ proj₂ (α p r))))

  -- the integral splits over the pieces (pieces-sum, then J-∑ for the series)
  ∫ᴹ-pieces : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) →
    ∫ᴹ {X} p f ≈ ∑ᶠ (λ n → bandW n * J (m p) (pieceψ {X} p n f) (pieceψ-Meas {X} p n f))
  ∫ᴹ-pieces {X} p f = trans
    (J-cong (m p) (mψ {X} p f) (Meas-∑ (pieceTerm {X} p f) (pieceTerm-Meas {X} p f)) (ψ-pieces {X} p f))
    (trans (J-∑ (m p) (pieceTerm {X} p f) (pieceTerm-Meas {X} p f))
      (∑ᶠ-cong (λ n → J-scale (m p) (bandW n) (pieceψ-Meas {X} p n f))))

  -- the probe of the X-component of `p`, as a morphism ℛ ⇒ X
  probeOf : ∀ {X : QBS S} → Pre (XW X) → Hom S (Probes.ℛQ S) X
  probeOf p = Probes.probe S (proj₂ (α-random p))

  -- the mass of a piece, and the piece as a probability measure (a fixed dummy when the mass is 0,
  -- `lem` decides which; `normM` otherwise)
  pieceMass : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Cut
  pieceMass p n = massM (pieceMeasure p n)

  Pos : Cut → Set
  Pos c = Σ RL.Q (λ s → RL.0Q ℚ.< s × memC c s)

  massM≤1 : ∀ ν → massM ν ≤ 1#
  massM≤1 ν = Measure.I-sub ν (Fun-const 1# ≤-refl)

  notPos-zero : ∀ c → (Pos c → ⊥) → c ≈ 0#
  notPos-zero c np = mk⊑ (λ q m → go m (RL.≤-or-> RL.0Q q)) , mk⊑ (λ q lt → negC c lt)
    where
      go : ∀ {q} → memC c q → RL.0Q ℚ.≤ q ⊎ q ℚ.< RL.0Q → q ℚ.< RL.0Q
      go m (inj₂ lt) = lt
      go {q} m (inj₁ le) with openC c m
      ... | q′ , q<q′ , mq′ = ⊥-elim (np (q′ , RL.≤-<-trans le q<q′ , mq′))

  -- the normalised measure when the mass is positive (`1/mass`), a dummy probability measure otherwise
  mass-inv : ∀ ν → Pos (massM ν) → massM ν * invC (massM ν) ≈ 1#
  mass-inv ν pos = trans (*-comm _ _) (InvClassical.inv-mul lem (massM ν) pos
    (RL.1Q , λ m → RL.<-irrefl RL.≃-refl (_⊑_.ap (massM≤1 ν) RL.1Q m)))

  probOfCase : ∀ ν → Pos (massM ν) ⊎ (Pos (massM ν) → ⊥) → Σ Measure IsProb
  probOfCase ν (inj₁ pos) = normM ν (invC (massM ν)) (mass-inv ν pos)
  probOfCase ν (inj₂ _) = dirac r₀ , IsProb-dirac r₀

  pieceProb : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Σ Measure IsProb
  pieceProb p n = probOfCase (pieceMeasure p n) (lem (Pos (pieceMass p n)))

  -- the integral against a density measure
  J-densityM : ∀ (m : Measure) (d : R₁ → Cut) (md : Meas d) (d≤1 : ∀ r → d r ≤ 1#) {φ} (mφ : Meas φ) →
    J (densityM m d md d≤1) φ mφ ≈ J m (λ r → d r * φ r) (Meas-⊗ {d} {φ} md mφ)
  J-densityM m d md d≤1 mφ = trans (J-dens m d md 1# (densityBd m d md d≤1) mφ) (*-identityˡ _)

  -- mass · (integral against the normalised measure) = integral against the measure
  probCase-int : ∀ (m : Measure) (d : R₁ → Cut) (md : Meas d) (d≤1 : ∀ r → d r ≤ 1#) {φ} (mφ : Meas φ) dec →
    massM (densityM m d md d≤1) * J (proj₁ (probOfCase (densityM m d md d≤1) dec)) φ mφ
      ≈ J m (λ r → d r * φ r) (Meas-⊗ {d} {φ} md mφ)
  probCase-int m d md d≤1 {φ} mφ (inj₁ pos) =
    trans (*-cong refl (trans (J-dens ν (const 1#) (Meas-const 1#) n (normBd ν n h) mφ)
                          (*-cong refl (trans (J-cong ν (Meas-⊗ {const 1#} {φ} (Meas-const 1#) mφ) mφ (λ r → *-identityˡ (φ r))) refl))))
      (trans (sym (*-assoc _ _ _)) (trans (*-cong h refl) (trans (*-identityˡ _) (J-densityM m d md d≤1 mφ))))
    where
      ν = densityM m d md d≤1
      n = invC (massM ν)
      h = mass-inv ν pos
  probCase-int m d md d≤1 {φ} mφ (inj₂ np) = trans (*-cong z refl) (trans (zeroˡ _) (sym zJ))
    where
      ν = densityM m d md d≤1
      z : massM ν ≈ 0#
      z = notPos-zero (massM ν) np
      Jd : J m d md ≈ 0#
      Jd = trans (sym (J-cong m (Mvh {d} {const 1#} md (Fun-const 1# ≤-refl)) md (λ r → *-identityʳ (d r))))
             (trans (sym (*-identityˡ _)) z)
      zJ : J m (λ r → d r * φ r) (Meas-⊗ {d} {φ} md mφ) ≈ 0#
      zJ = J-null m d md mφ Jd

  -- mass · (integral against the normalised piece) = integral against the piece; both sides vanish when the mass is 0
  pieceProb-int : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) (f : Hom S X WQ) →
    pieceMass p n * J (proj₁ (pieceProb p n)) (λ r → map f ⟨$⟩ proj₂ (α p r))
      (map-random f (proj₂ (α-random p)))
    ≈ J (m p) (pieceψ {X} p n f) (pieceψ-Meas {X} p n f)
  pieceProb-int {X} p n f = probCase-int (m p) (pieceDensity p n) (pieceDensity-Meas p n) (pieceDensity≤1 p n)
    (map-random f (proj₂ (α-random p))) (lem (Pos (pieceMass p n)))

  ----------------------------------------------------------------------------
  -- 3. the decomposition

  -- the law of the probe `a` under a probability measure, as a pre-measure of the probability monad
  lawPre : ∀ {X : QBS S} → Hom S (Probes.ℛQ S) X → Σ Measure IsProb → C.Pre X
  lawPre a (μ , pμ) = mk (λ r → map a ⟨$⟩ r) (Probes.unprobe S a) μ pμ

  -- the n-th scaled law
  decomp-term : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) (f : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} (bandW n * pieceMass p n) (ιPre {X} (lawPre (probeOf p) (pieceProb p n)))) f
    ≈ bandW n * J (m p) (pieceψ {X} p n f) (pieceψ-Meas {X} p n f)
  decomp-term {X} p n f = trans (∫ᴹ-scale {X} (bandW n * pieceMass p n) (ιPre {X} (lawPre (probeOf p) (pieceProb p n))) f)
    (trans (*-cong refl (J-cong (proj₁ (pieceProb p n))
        (mψ {X} (ιPre {X} (lawPre (probeOf p) (pieceProb p n))) f)
        (map-random f (proj₂ (α-random p))) (λ r → *-identityˡ _)))
      (trans (*-assoc _ _ _) (*-cong refl (pieceProb-int {X} p n f))))

  scaledLawsPre : ∀ {X : QBS S} (p : Pre (XW X)) →
    Σ (ℕ → Hom S (Probes.ℛQ S) X) λ a →
    Σ (ℕ → ∣ WQ ∣) λ c →
    Σ (ℕ → Σ Measure IsProb) λ μ →
      ∀ (f : Hom S X WQ) → ∫ᴹ {X} p f ≈ ∑ᶠ (λ n → ∫ᴹ {X} (scalePre {X} (c n) (ιPre {X} (lawPre (a n) (μ n)))) f)
  scaledLawsPre {X} p = (λ n → probeOf p) , (λ n → bandW n * pieceMass p n) , (λ n → pieceProb p n) ,
    (λ f → trans (∫ᴹ-pieces {X} p f) (∑ᶠ-cong (λ n → sym (decomp-term {X} p n f))))

  -- (the global-element form, with `law` of `ContinuousProb`, is assembled in `SFiniteStat`)
