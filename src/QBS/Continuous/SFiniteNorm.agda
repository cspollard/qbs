{-# OPTIONS --safe --without-K #-}

-- Normalisation `M X ⇒ Prob X + 1` of s-finite measures, with its three laws.
--
-- The mass `∫ᴹ p 1` of `[α, m, w]` is a lower real in `[0, ∞]`; classically it is either invertible
-- (finite and positive, `Analysis/LowerInverse`) or not (zero or infinite).  Invertible: normalise by
-- the inverse, which is again a pre-measure `[α, m, w/mass]`, here with `w` rebuilt to a probability
-- by pushing the weight into the measure (`Continuous/SFiniteDecomp.normM` on the level pieces).  Not
-- invertible: fail (`inj₂ tt`); the degenerate infinite-mass case is left unspecified by the interface.

module QBS.Continuous.SFiniteNorm where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ; !Q)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘; Cantor; Borel; compl; resp; union₂; inter₂; ⊥-borel; Partition)
open import QBS.Borel.Source using (R₁; cantorSource; down; downℕ; idxₛ)
open import Data.Product.Function.NonDependent.Setoid using (proj₂ₛ)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (Cut)
import QBS.Analysis.LowerReals as LR
open LR.Cut using () renaming (mem to memC)
open LR._⊑_ using () renaming (ap to apC)
import QBS.Analysis.RationalLemmas as RL
import Data.Rational.Unnormalised.Base as ℚ
import QBS.Analysis.LowerInverse as LI
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Analysis.Density using (module Density)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.MeasFun using (module MeasFun)
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
import Data.Nat.Base as ℕ
open import QBS.Continuous.Strong using (module Strength)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import QBS.Classical using (LEM₀)

module SFiniteNorm (lem : LEM₀) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Density lem using (densM; J-dens)
  open LevelSets lem using (LS; Lvl; borel-prop)
  open MeasFun lem using (Meas→Fun)
  open Weights lem using (WQ; mulW; constW; oneW; zero⇒)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open UnitInterval A using (AQ)
  open RandomSource S using (Rˢ) renaming (meas-id to measId)
  open SFinite lem
  open WitM
  open SFiniteMonad lem
  open SFiniteStrong lem
  open SFiniteSum lem
  open SFiniteIncl lem
  open Series A
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  open import Data.Sum.Base using (inj₁; inj₂)

  private
    oneF : ∀ (X : QBS S) → Hom S X WQ
    oneF X = constW 1#

  -- total massP of a pre-measure
  massP : ∀ {X : QBS S} → Pre (XW X) → Cut
  massP {X} p = ∫ᴹ {X} p (oneF X)

  massP-cong : ∀ {X : QBS S} {p q : Pre (XW X)} → _≈ᴹ_ {X} p q → massP p ≈ massP q
  massP-cong {X} {p} {q} e = e (oneF X)

  massP-scale : ∀ {X : QBS S} c (p : Pre (XW X)) → massP (scalePre {X} c p) ≈ c * massP p
  massP-scale {X} c p = ∫ᴹ-scale {X} c p (oneF X)

  -- the decision "is the massP invertible?", classical (`lem`)
  InvDec : Cut → Set₁
  InvDec m = Σ Cut (λ n → m * n ≈ 1#) ⊎ (∀ n → m * n ≈ 1# → ⊥)

  -- rational-level (Set) conditions for invertibility: a positive member and a non-member
  PosC FinC : Cut → Set
  PosC m = Σ RL.ℚᵘ (λ s → RL.0ℚᵘ RL.<ᵘ s × memC m s)
  FinC m = Σ RL.ℚᵘ (λ ρ → memC m ρ → ⊥)

  -- an inverse pair has positive members on both sides
  inv-pos : ∀ m n → m * n ≈ 1# →
    Σ RL.ℚᵘ (λ a → Σ RL.ℚᵘ (λ b → RL.0ℚᵘ RL.<ᵘ a × RL.0ℚᵘ RL.<ᵘ b × memC m a × memC n b))
  inv-pos m n h = go (RL.dense RL.0<1)
    where
      go : Σ RL.ℚᵘ (λ r → RL.0ℚᵘ RL.<ᵘ r × r RL.<ᵘ RL.1ℚᵘ) → _
      go (r , 0<r , r<1) = cs (apC (proj₂ h) r r<1)
        where
          cs : memC (m LR.⊗ n) r → _
          cs (inj₁ lt) = ⊥-elim (RL.<-irrefl RL.≃-refl (RL.<-trans 0<r lt))
          cs (inj₂ (a , b , 0<a , 0<b , ma , mb , _)) = a , b , 0<a , 0<b , ma , mb

  inv-fin : ∀ m n → m * n ≈ 1# → FinC m
  inv-fin m n h with lem (FinC m)
  ... | inj₁ f = f
  ... | inj₂ nof with inv-pos m n h
  ... | a , b , 0<a , 0<b , ma , mb = ⊥-elim (RL.<-irrefl RL.≃-refl (apC (proj₁ h) RL.1ℚᵘ one-mem))
    where
      all : ∀ ρ → memC m ρ
      all ρ with lem (memC m ρ)
      ... | inj₁ yes = yes
      ... | inj₂ no = ⊥-elim (nof (ρ , no))
      t = proj₁ (RL.inv 0<b)
      ht = proj₂ (RL.inv 0<b)
      one-mem : memC (m LR.⊗ n) RL.1ℚᵘ
      one-mem = inj₂ (t , b , LI.pos-of-inverse 0<b ht , 0<b , all t , mb , RL.≤-≃ (RL.≃-sym ht))

  invDec′ : ∀ m → (PosC m × FinC m) ⊎ ((PosC m × FinC m) → ⊥) → InvDec m
  invDec′ m (inj₁ (p , f)) = inj₁ (LI.invC m , trans (*-comm m (LI.invC m)) (LI.InvClassical.inv-mul lem m p f))
  invDec′ m (inj₂ no) = inj₂ (λ n h → no (let a , b , 0<a , _ , ma , _ = inv-pos m n h in (a , 0<a , ma) , inv-fin m n h))

  invDec : ∀ m → InvDec m
  invDec m = invDec′ m (lem (PosC m × FinC m))

  -- the weight of a pre-measure, as a function on the parameter space
  wP : ∀ {X : QBS S} → Pre (XW X) → R₁ → Cut
  wP p r = proj₁ (α p ⟨$⟩ r)

  mwP : ∀ {X : QBS S} (p : Pre (XW X)) → Meas (wP {X} p)
  mwP p = proj₁ (α-random p)

  massP-J : ∀ {X : QBS S} (p : Pre (XW X)) → massP {X} p ≈ J (m p) (wP {X} p) (mwP {X} p)
  massP-J {X} p = J-cong (m p) (mψ {X} p (oneF X)) (mwP {X} p) (λ r → *-identityʳ _)

  oneJ : ∀ {X : QBS S} (p : Pre (XW X)) (pf : Meas (λ r → wP {X} p r * 1#)) →
    J (m p) (λ r → wP {X} p r * 1#) pf ≈ massP {X} p
  oneJ {X} p pf = trans (J-cong (m p) pf (mwP {X} p) (λ r → *-identityʳ _)) (sym (massP-J {X} p))

  normBd : ∀ {X : QBS S} (p : Pre (XW X)) (n : Cut) → massP {X} p * n ≈ 1# →
    n * J (m p) (wP {X} p) (mwP {X} p) ≤ 1#
  normBd {X} p n h = ≤-reflexive (trans (*-comm n _) (trans (*-cong (sym (massP-J {X} p)) refl) h))

  -- the normalised measure on R: density `w` against `m`, scaled by the inverse of the mass
  normMeas : ∀ {X : QBS S} (p : Pre (XW X)) (n : Cut) → massP {X} p * n ≈ 1# → Measure
  normMeas {X} p n h = densM (m p) (wP {X} p) (mwP {X} p) n (normBd {X} p n h)

  normMeas-prob : ∀ {X : QBS S} (p : Pre (XW X)) (n : Cut) (h : massP {X} p * n ≈ 1#) →
    IsProb (normMeas {X} p n h)
  normMeas-prob {X} p n h = trans (*-cong refl (oneJ {X} p _)) (trans (*-comm n _) h)

  -- normalisation of a measure of invertible massP: a probability pre-measure on X
  normPre : ∀ {X : QBS S} (p : Pre (XW X)) (n : Cut) → massP p * n ≈ 1# → C.Pre X
  normPre {X} p n h = mk (proj₂ₛ ∘ₛ α p) (proj₂ (α-random p)) (normMeas {X} p n h) (normMeas-prob {X} p n h)

  ∫-normPre : ∀ {X : QBS S} (p : Pre (XW X)) (n : Cut) (h : massP p * n ≈ 1#) (f : Hom S X WQ) →
    ∫ᴹ {X} (ιPre {X} (normPre p n h)) f ≈ n * ∫ᴹ {X} p f
  ∫-normPre {X} p n h f = trans
    (J-dens (m p) (wP {X} p) (mwP {X} p) n (normBd {X} p n h) (mψ {X} (ιPre {X} (normPre {X} p n h)) f))
    (*-cong refl (J-cong (m p) _ (mψ {X} p f) (λ r → *-cong refl (*-identityˡ _))))

  ----------------------------------------------------------------------------
  -- algebra of inverses

  inv-unique : ∀ {x n n′} → x * n ≈ 1# → x * n′ ≈ 1# → n ≈ n′
  inv-unique {x} {n} {n′} h h′ = trans (sym (*-identityˡ n))
    (trans (*-cong (sym h′) refl)
      (trans (*-assoc x n′ n)
        (trans (*-cong refl (*-comm n′ n))
          (trans (sym (*-assoc x n n′))
            (trans (*-cong h refl) (*-identityˡ n′))))))

  inv-resp : ∀ {x y n} → x ≈ y → x * n ≈ 1# → y * n ≈ 1#
  inv-resp e h = trans (*-cong (sym e) refl) h

  open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup using () renaming (x∙yz≈y∙xz to swap*)

  scale-inv₁ : ∀ x n′ c → (c * x) * n′ ≈ 1# → x * (n′ * c) ≈ 1#
  scale-inv₁ x n′ c h = trans (*-cong refl (*-comm n′ c)) (trans (swap* x c n′) (trans (sym (*-assoc c x n′)) h))

  scale-inv₂ : ∀ c d x n → c * d ≈ 1# → x * n ≈ 1# → (c * x) * (d * n) ≈ 1#
  scale-inv₂ c d x n cd h = trans (*-assoc c x (d * n))
    (trans (*-cong refl (swap* x d n))
      (trans (sym (*-assoc c d (x * n))) (trans (*-cong cd h) (*-identityˡ 1#))))

  zero≉one : 0# ≈ 1# → ⊥
  zero≉one h = go (RL.dense RL.0<1)
    where
      go : Σ RL.ℚᵘ (λ r → RL.0ℚᵘ RL.<ᵘ r × r RL.<ᵘ RL.1ℚᵘ) → ⊥
      go (r , 0<r , r<1) = RL.<-irrefl RL.≃-refl (RL.<-trans 0<r (apC (proj₂ h) r r<1))

  ----------------------------------------------------------------------------
  -- bounded and weighted integrals of probability pre-measures agree

  coeH : ∀ {X : QBS S} → Hom S X AQ → Hom S X WQ
  coeH {X} hh = record
    { map = record { to = λ x → proj₁ (map hh ⟨$⟩ x) ; cong = λ e → Func.cong (map hh) e }
    ; map-random = λ {γ} rγ → LS (map-random hh rγ)
    }

  ∫-vs-ᴹ : ∀ {X : QBS S} (q : C.Pre X) (hh : Hom S X AQ) →
    C.∫ {X} q hh ≈ ∫ᴹ {X} (ιPre {X} q) (coeH {X} hh)
  ∫-vs-ᴹ {X} q hh = trans (sym (J-fun (m q) (map-random hh (α-random q))))
    (J-cong (m q) (LS (map-random hh (α-random q))) (mψ {X} (ιPre {X} q) (coeH {X} hh)) (λ r → sym (*-identityˡ _)))

  ι-reflect : ∀ {X : QBS S} {q₁ q₂ : C.Pre X} →
    (∀ f → ∫ᴹ {X} (ιPre {X} q₁) f ≈ ∫ᴹ {X} (ιPre {X} q₂) f) → C._≈ᵖ_ {X} q₁ q₂
  ι-reflect {X} {q₁} {q₂} e hh = trans (∫-vs-ᴹ {X} q₁ hh) (trans (e (coeH {X} hh)) (sym (∫-vs-ᴹ {X} q₂ hh)))

  -- the mass of a probability measure is 1
  mass-ι : ∀ {X : QBS S} (p : C.Pre X) → massP {X} (ιPre {X} p) ≈ 1#
  mass-ι {X} p = trans (J-cong (m p) (mψ {X} (ιPre {X} p) (oneF X)) (LS (Fun-const 1# ≤-refl)) (λ r → *-identityˡ _))
    (trans (J-fun (m p) (Fun-const 1# ≤-refl)) (ok p))

  -- normalisation respects the equality of measures
  normPre-≈ : ∀ {X : QBS S} {p q : Pre (XW X)} (e : _≈ᴹ_ {X} p q) (n n′ : Cut)
    (h : massP {X} p * n ≈ 1#) (h′ : massP {X} q * n′ ≈ 1#) →
    C._≈ᵖ_ {X} (normPre {X} p n h) (normPre {X} q n′ h′)
  normPre-≈ {X} {p} {q} e n n′ h h′ = ι-reflect {X} λ f →
    trans (∫-normPre {X} p n h f)
      (trans (*-cong refl (e f))
        (trans (*-cong (inv-unique {massP {X} p} h (inv-resp (sym (massP-cong {X} {p} {q} e)) h′)) refl)
          (sym (∫-normPre {X} q n′ h′ f))))

  normC′ : ∀ {X : QBS S} (p : Pre (XW X)) → InvDec (massP p) → ∣ C.TQ X ∣ ⊎ ∣ 1Q S ∣
  normC′ p (inj₁ (n , h)) = inj₁ (normPre p n h)
  normC′ p (inj₂ _) = inj₂ tt

  normC : ∀ {X : QBS S} → Pre (XW X) → ∣ C.TQ X ∣ ⊎ ∣ 1Q S ∣
  normC p = normC′ p (invDec (massP p))

  normC′-cong : ∀ {X : QBS S} {p q : Pre (XW X)} → _≈ᴹ_ {X} p q → (d : InvDec (massP p)) (d′ : InvDec (massP q)) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ p d) (normC′ q d′)
  normC′-cong {X} {p} {q} e (inj₁ (n , h)) (inj₁ (n′ , h′)) = ⊎ʳ.inj₁ (normPre-≈ {X} {p} {q} e n n′ h h′)
  normC′-cong {X} {p} {q} e (inj₁ (n , h)) (inj₂ no) = ⊥-elim (no n (inv-resp (massP-cong {X} {p} {q} e) h))
  normC′-cong {X} {p} {q} e (inj₂ no) (inj₁ (n′ , h′)) = ⊥-elim (no n′ (inv-resp (sym (massP-cong {X} {p} {q} e)) h′))
  normC′-cong e (inj₂ _) (inj₂ _) = ⊎ʳ.inj₂ (Setoid.refl (Carrier (1Q S)))

  normC-cong : ∀ {X : QBS S} {p q : Pre (XW X)} → _≈ᴹ_ {X} p q →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC p) (normC q)
  normC-cong {X} {p} {q} e = normC′-cong {X} {p} {q} e (invDec (massP p)) (invDec (massP q))

  -- the case index of a measure: 0 = invertible massP (normalise), 1 = not (fail)
  caseOf : ∀ {m} → InvDec m → ℕ
  caseOf (inj₁ _) = ℕ.zero
  caseOf (inj₂ _) = ℕ.suc ℕ.zero

  caseIdx : ∀ {X : QBS S} → Pre (XW X) → ℕ
  caseIdx p = caseOf (invDec (massP p))

  -- the classical inverse
  inv-ok : ∀ m → PosC m → FinC m → m * LI.invC m ≈ 1#
  inv-ok m p f = trans (*-comm m (LI.invC m)) (LI.InvClassical.inv-mul lem m p f)

  inv-ok′ : ∀ m n → m * n ≈ 1# → m * LI.invC m ≈ 1#
  inv-ok′ m n h = inv-ok m (let a , b , 0<a , _ , ma , _ = inv-pos m n h in a , 0<a , ma) (inv-fin m n h)

  case0-to : ∀ {m} (d : InvDec m) → caseOf d ≡.≡ ℕ.zero → PosC m × FinC m
  case0-to {m} (inj₁ (n , h)) _ = let a , b , 0<a , _ , ma , _ = inv-pos m n h in (a , 0<a , ma) , inv-fin m n h
  case0-to (inj₂ _) ()

  case0-from : ∀ {m} (d : InvDec m) → PosC m × FinC m → caseOf d ≡.≡ ℕ.zero
  case0-from (inj₁ _) _ = ≡.refl
  case0-from {m} (inj₂ no) (p , f) = ⊥-elim (no (LI.invC m) (inv-ok m p f))

  case1-to : ∀ {m} (d : InvDec m) → caseOf d ≡.≡ ℕ.suc ℕ.zero → (PosC m × FinC m → ⊥)
  case1-to (inj₁ _) ()
  case1-to {m} (inj₂ no) _ = λ pf → no (LI.invC m) (inv-ok m (proj₁ pf) (proj₂ pf))

  case1-from : ∀ {m} (d : InvDec m) → (PosC m × FinC m → ⊥) → caseOf d ≡.≡ ℕ.suc ℕ.zero
  case1-from {m} (inj₁ (n , h)) npf = ⊥-elim
      (npf ((let a , b , 0<a , _ , ma , _ = inv-pos m n h in a , 0<a , ma) , inv-fin m n h))
  case1-from (inj₂ _) _ = ≡.refl

  case2 : ∀ {m} (d : InvDec m) (k : ℕ) → caseOf d ≡.≡ ℕ.suc (ℕ.suc k) → ⊥
  case2 (inj₁ _) k ()
  case2 (inj₂ _) k ()

  -- r ↦ massP (β r) is `Meas` (`∫ᶠ` is a test function on measures, so it preserves random families)
  massP-Meas : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → WitM {X} β → Meas (λ r → massP (β r))
  massP-Meas {X} {β} w = ∫ᴹ-Meas {X} {β} w (oneF X)

  -- measurability: {r | massP (β r) invertible} is Borel, since r ↦ massP (β r) is `Meas`
  -- (`Tonelli.Meas-J`) and 0 < m < ∞ is a countable union of intersections of threshold sets
  caseIdx-Idx : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → WitM {X} β → Partition (downℕ (λ r → caseIdx (β r)))
  caseIdx-Idx {X} {β} w = idx
    where
      M : R₁ → Cut
      M r = massP {X} (β r)

      bPF : Borel (λ (c : Cantor) → PosC (M (L.lift c)) × FinC (M (L.lift c)))
      bPF = inter₂ (ex-enum (λ s c → RL.0ℚᵘ RL.<ᵘ s × Lvl M s c) (λ s → inter₂ (borel-prop _) (massP-Meas {X} {β} w s)))
                   (ex-enum (λ ρ c → Lvl M ρ c → ⊥) (λ ρ → compl (massP-Meas {X} {β} w ρ)))

      idx : ∀ k → Borel (λ (c : Cantor) → caseIdx {X} (β (L.lift c)) ≡.≡ k)
      idx ℕ.zero = resp (λ c → case0-from (invDec (M (L.lift c))) , case0-to (invDec (M (L.lift c)))) bPF
      idx (ℕ.suc ℕ.zero) = resp (λ c → case1-from (invDec (M (L.lift c))) , case1-to (invDec (M (L.lift c)))) (compl bPF)
      idx (ℕ.suc (ℕ.suc k)) = resp (λ c → (λ ()) , case2 (invDec (M (L.lift c))) k) ⊥-borel

  -- the classical inverse as a function (the cut `invC`; it is an inverse exactly when the mass is invertible)
  invOf : Cut → Cut
  invOf m = LI.invC m

  invOf-Meas : ∀ {f : R₁ → Cut} → Meas f → Meas (λ r → invOf (f r))
  invOf-Meas {f} mf q =
    union₂ (borel-prop (q RL.<ᵘ RL.0ℚᵘ))
      (ex-enum (λ ρ c → RL.0ℚᵘ RL.<ᵘ ρ × ((memC (f (L.lift c)) ρ → ⊥) × (q ℚ.* ρ) RL.<ᵘ RL.1ℚᵘ))
        (λ ρ → inter₂ (borel-prop _) (inter₂ (compl (mf ρ)) (borel-prop _))))

  -- on the invertible case, the normalised family is a random element of C.TQ X:
  -- the joint probe keeps only the point of the weighted probe, and the kernel normalises the section measures
  module NormW {X : QBS S} {β : R₁ → Pre (XW X)} (w : WitM {X} β)
    (inv : ∀ r → massP {X} (β r) * invOf (massP {X} (β r)) ≈ 1#) where

    nN : R₁ → Cut
    nN r = invOf (massP {X} (β r))

    kP : R₁ → Pre (XW X)
    kP r = kerP {X} (a w) (g w) (g-pr w) r

    hK : ∀ r → massP {X} (kP r) * nN r ≈ 1#
    hK r = inv-resp (massP-cong {X} {β r} {kP r} (w-eq w r)) (inv r)

    gN : R₁ → Measure
    gN r = normMeas {X} (kP r) (nN r) (hK r)

    gN-pr : ∀ r → IsProb (gN r)
    gN-pr r = normMeas-prob {X} (kP r) (nN r) (hK r)

    aN : Joint X
    aN = record
      { map = record { to = λ p → proj₂ (map (a w) ⟨$⟩ p) ; cong = λ e → proj₂ (Func.cong (map (a w)) e) }
      ; map-random = λ {γ} mr → proj₂ (map-random (a w) mr)
      }

    φN : (R₁ → Cut) → R₁ → Cut
    φN h k = proj₁ (map (a w) ⟨$⟩ (evensR k , oddsR k)) * h (oddsR k)

    mφN : ∀ {h} → Fun h → Meas (φN h)
    mφN {h} fh = Meas-⊗ {λ k → proj₁ (map (a w) ⟨$⟩ (evensR k , oddsR k))} {λ k → h (oddsR k)}
      (proj₁ (paJ {X} (a w))) (Meas-pre {h} {oddsR} (LS fh) measurable-odds)

    φN-sec : ∀ {h} → Fun h → ∀ r s → φN h (mergeR r s) ≈ proj₁ (map (a w) ⟨$⟩ (r , s)) * h s
    φN-sec fh r s = *-cong (proj₁ (Func.cong (map (a w)) (merge-evens r s , merge-odds r s)))
                           (Meas-resp (LS fh) (lower (merge-odds r s)))

    srcMeas : ∀ {h} (fh : Fun h) → Meas (λ r → nN r * J (g w r) (λ s → φN h (mergeR r s))
                                        (Meas-pre {φN h} {mergeR r} (mφN fh) (measurable-merge₁ (lower r))))
    srcMeas {h} fh = Meas-⊗ {nN} {λ r → J (g w r) (λ s → φN h (mergeR r s))
                                      (Meas-pre {φN h} {mergeR r} (mφN fh) (measurable-merge₁ (lower r)))}
      (invOf-Meas {λ r → massP {X} (β r)} (massP-Meas {X} {β} w)) (Meas-Jsec (g w) (g-ok w) {φN h} (mφN fh))

    meas-int : ∀ {h} (fh : Fun h) → Meas (λ r → I (gN r) h fh)
    meas-int {h} fh = Meas-ext {λ r → nN r * J (g w r) (λ s → φN h (mergeR r s))
                                        (Meas-pre {φN h} {mergeR r} (mφN fh) (measurable-merge₁ (lower r)))}
      {λ r → I (gN r) h fh} (λ r → *-cong refl (J-cong (g w r) _ _ (φN-sec fh r))) (srcMeas fh)

    g-ok-N : KernelOk gN
    g-ok-N {h} fh = Meas→Fun bound (meas-int fh)
      where
        bound : ∀ r → I (gN r) h fh ≤ 1#
        bound r = ≤-trans (I-mono (gN r) fh (Fun-const 1# ≤-refl) (Fun-≤1 fh)) (≤-reflexive (gN-pr r))

    weqN : ∀ r → C._≈ᵖ_ {X} (normPre {X} (β r) (nN r) (inv r))
      (mk {X} (sec {X} aN r) (sec-random {X} aN r) (gN r) (gN-pr r))
    weqN r f = trans
      (normPre-≈ {X} {β r} {kP r} (w-eq w r) (nN r) (nN r) (inv r) (hK r) f)
      (C.rand-irrel {X} {sec {X} aN r} (proj₂ (sec-random {XW X} (a w) r)) (sec-random {X} aN r) (gN r) (gN-pr r) f)

  normPre-random : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → WitM {X} β →
    (inv : ∀ r → massP (β r) * invOf (massP (β r)) ≈ 1#) →
    C.Wit {X} (λ r → normPre (β r) (invOf (massP (β r))) (inv r))
  normPre-random {X} {β} w inv = record
    { a = NormW.aN w inv ; g = NormW.gN w inv ; g-ok = NormW.g-ok-N w inv
    ; g-pr = NormW.gN-pr w inv ; w-eq = NormW.weqN w inv }

  -- gluing: on the invertible part normalise (`normPre-random` for a repaired family), elsewhere fail
  module NormGlue {X : QBS S} {β : R₁ → Pre (XW X)} (w : WitM {X} β) where
    x₀ : ∣ X ∣
    x₀ = proj₂ (α (β r₀) ⟨$⟩ r₀)

    -- a measure of mass 1, used where the mass is not invertible
    dummy : Pre (XW X)
    dummy = C.ηPre {XW X} (1# , x₀)

    massP-dummy : massP {X} dummy ≈ 1#
    massP-dummy = ∫ᴹ-η {X} x₀ (oneF X)

    pick : ℕ → R₁ → Pre (XW X)
    pick ℕ.zero r = β r
    pick (ℕ.suc _) r = dummy

    ws : ∀ n → WitM {X} (pick n)
    ws ℕ.zero = w
    ws (ℕ.suc _) = TQ-const {X} dummy

    w̃ : WitM {X} (λ r → pick (caseIdx {X} (β r)) r)
    w̃ = TQ-glue {X} {idxₛ (λ r → caseIdx {X} (β r)) (caseIdx-Idx {X} {β} w)} (caseIdx-Idx {X} {β} w) pick ws

    inṽ-aux : ∀ r (d : InvDec (massP {X} (β r))) →
      massP {X} (pick (caseOf d) r) * invOf (massP {X} (pick (caseOf d) r)) ≈ 1#
    inṽ-aux r (inj₁ (n , h)) = inv-ok′ (massP {X} (β r)) n h
    inṽ-aux r (inj₂ _) = inv-ok′ (massP {X} dummy) 1# (trans (*-cong massP-dummy refl) (*-identityˡ 1#))

    inṽ : ∀ r → massP {X} (pick (caseIdx {X} (β r)) r) * invOf (massP {X} (pick (caseIdx {X} (β r)) r)) ≈ 1#
    inṽ r = inṽ-aux r (invDec (massP {X} (β r)))

    τ′ : ∀ r (d : InvDec (massP {X} (β r))) → C.Pre X
    τ′ r d = normPre {X} (pick (caseOf d) r) (invOf (massP {X} (pick (caseOf d) r))) (inṽ-aux r d)

    τ : R₁ → C.Pre X
    τ r = normPre {X} (pick (caseIdx {X} (β r)) r) (invOf (massP {X} (pick (caseIdx {X} (β r)) r))) (inṽ r)

    τ-random : C.Wit {X}
        (λ r → normPre {X} (pick (caseIdx {X} (β r)) r) (invOf (massP {X} (pick (caseIdx {X} (β r)) r))) (inṽ r))
    τ-random = normPre-random {X} {λ r → pick (caseIdx {X} (β r)) r} w̃ inṽ

    τ′-ok : ∀ r (e : InvDec (massP {X} (β r))) (n : Cut) (h : massP {X} (β r) * n ≈ 1#) →
      e ≡.≡ inj₁ (n , h) → C._≈ᵖ_ {X} (normPre {X} (β r) n h) (τ′ r e)
    τ′-ok r .(inj₁ (n , h)) n h ≡.refl = normPre-≈ {X} {β r} {β r} (λ f → refl) n (invOf (massP {X} (β r))) h
        (inṽ-aux r (inj₁ (n , h)))

    c : ℕ → Piece S (C.TQ X) (1Q S)
    c ℕ.zero = inj₁ (C.witₛ {X} τ-random , τ-random)
    c (ℕ.suc _) = inj₂ (constₛ tt , QBS.const-random (1Q S) tt)

    pf-aux : ∀ r (d : InvDec (massP {X} (β r))) → invDec (massP {X} (β r)) ≡.≡ d →
      Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ (β r) d) (ev S (C.TQ X) (1Q S) (c (caseOf d)) r)
    pf-aux r (inj₁ (n , h)) eq = ⊎ʳ.inj₁ (τ′-ok r (invDec (massP {X} (β r))) n h eq)
    pf-aux r (inj₂ _) eq = ⊎ʳ.inj₂ (Setoid.refl (Carrier (1Q S)))

  normCₛ : ∀ {X : QBS S} → Func (Carrier (TQ X)) (Carrier (_+Q_ S (C.TQ X) (1Q S)))
  normCₛ = record { to = normC ; cong = normC-cong }

  normRandom : ∀ {X : QBS S} {β : Func Rˢ (Carrier (TQ X))} → WitM {X} (β ⟨$⟩_) →
    QBS.Random (_+Q_ S (C.TQ X) (1Q S)) (normCₛ ∘ₛ β)
  normRandom {X} {β} w = idxₛ (λ r → caseIdx {X} (β ⟨$⟩ r)) (caseIdx-Idx {X} {β ⟨$⟩_} w) , caseIdx-Idx {X} {β ⟨$⟩_} w ,
    NormGlue.c w , (λ r → NormGlue.pf-aux w r (invDec (massP {X} (β ⟨$⟩ r))) ≡.refl)

  normH : ∀ X → Hom S (TQ X) (_+Q_ S (C.TQ X) (1Q S))
  normH X = record { map = normCₛ ; map-random = λ {β} → normRandom {X} {β} }

  -- the three laws
  normProb : ∀ {X : QBS S} (p : C.Pre X) (e : InvDec (massP (ιPre {X} p))) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ (ιPre {X} p) e) (inj₁ p)
  normProb {X} p (inj₁ (n , h)) = ⊎ʳ.inj₁ (ι-reflect {X} λ f →
    trans (∫-normPre {X} (ιPre {X} p) n h f)
      (trans (*-cong (inv-unique {massP {X} (ιPre {X} p)} h (trans (*-cong (mass-ι {X} p) refl) (*-identityˡ 1#)) ) refl)
        (*-identityˡ _)))
  normProb {X} p (inj₂ no) = ⊥-elim (no 1# (trans (*-cong (mass-ι {X} p) refl) (*-identityˡ 1#)))

  normZero : ∀ {X : QBS S} (p : Pre (XW X)) → massP p ≈ 0# → (e : InvDec (massP p)) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ p e) (inj₂ tt)
  normZero p z (inj₁ (n , h)) = ⊥-elim (zero≉one (trans (sym (zeroˡ n)) (trans (*-cong (sym z) refl) h)))
  normZero p z (inj₂ _) = ⊎ʳ.inj₂ (Setoid.refl (Carrier (1Q S)))

  normScale : ∀ {X : QBS S} (c d : Cut) → c * d ≈ 1# → (p : Pre (XW X))
    (e′ : InvDec (massP (scalePre {X} c p))) (e : InvDec (massP p)) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ (scalePre {X} c p) e′) (normC′ p e)
  normScale {X} c d cd p (inj₁ (n′ , h′)) (inj₁ (n , h)) = ⊎ʳ.inj₁ (ι-reflect {X} λ f →
    trans (∫-normPre {X} (scalePre {X} c p) n′ h′ f)
      (trans (*-cong refl (∫ᴹ-scale {X} c p f))
        (trans (sym (*-assoc n′ c _))
          (trans (*-cong (inv-unique {massP {X} p} (scale-inv₁ (massP {X} p) n′ c (hc′ {X} c p n′ h′)) h) refl)
            (sym (∫-normPre {X} p n h f))))))
    where
      hc′ : ∀ {X : QBS S} c (p : Pre (XW X)) n′ → massP {X} (scalePre {X} c p) * n′ ≈ 1# → (c * massP {X} p) * n′ ≈ 1#
      hc′ {X} c p n′ h′ = inv-resp (massP-scale {X} c p) h′
  normScale {X} c d cd p (inj₁ (n′ , h′)) (inj₂ no) =
    ⊥-elim (no (n′ * c) (scale-inv₁ (massP {X} p) n′ c (inv-resp (massP-scale {X} c p) h′)))
  normScale {X} c d cd p (inj₂ no′) (inj₁ (n , h)) =
    ⊥-elim (no′ (d * n) (inv-resp (sym (massP-scale {X} c p)) (scale-inv₂ c d (massP {X} p) n cd h)))
  normScale c d cd p (inj₂ _) (inj₂ _) = ⊎ʳ.inj₂ (Setoid.refl (Carrier (1Q S)))

