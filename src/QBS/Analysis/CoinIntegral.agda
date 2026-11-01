{-# OPTIONS --safe --without-K #-}

-- The integral against the fair-coin measure of every measurable function: the supremum of the
-- integrals of the simple functions below it (resized to Set with a classical axiom at Set₁), and
-- the proof that it is a Daniell functional (`Measure`) agreeing with the dyadic premeasure.
module QBS.Analysis.CoinIntegral where

import Level as L
import Data.Nat.Properties as ℕₚ
open import Level using (Lift; lift; lower)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Data.Rational.Unnormalised.Base using (_<_)
open import Data.Rational.Unnormalised.Base using () renaming (_*_ to _*ᵘ_; _+_ to _+ᵘ_; _≤_ to _≤ᵘ_; _≃_ to _≃ᵘ_)
import QBS.Analysis.RationalLemmas as RL
open RL using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; dense; ≤-<-trans; nat-nonneg)
open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Model.Pairing using (unpair)
open import QBS.Analysis.Omega
open import QBS.Analysis.Series
import QBS.Analysis.SeriesSup as SeriesSup
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (Cut; _⊑_; mk⊑; _≋_; zeroC; oneC; LowerRealsOmega; ⊗-mono)
open import QBS.Analysis.LowerRealsArch using (arch-⊑; hpC; hpC-double; tp; tp-pos; tp-small; lowerRealsArch)
open import QBS.Analysis.Archimedean
open import QBS.Analysis.BorelMeasure
open import QBS.Analysis.CoinSimple
open import QBS.Analysis.CoinCont
open import QBS.Analysis.LevelSets
open import QBS.Analysis.CoinGrid
open import QBS.Classical using (LEM₀; LEM₁)
open Cut
open _⊑_

-- a pure rational estimate used for scaling
smallprod : ∀ {N tk tn r y q : ℚᵘ} → 0ℚᵘ < N → 0ℚᵘ < y → r < N → y ≤ᵘ tk → N *ᵘ tk < tn → q ≤ᵘ r *ᵘ y → q < tn
smallprod {N} 0<N 0<y r<N y≤tk Ntk<tn le =
  RL.≤-<-trans le (RL.<-trans (RL.<-≤-trans (RL.*-mono-<-posʳ 0<y r<N) (RL.*-mono-≤-nn (RL.<-≤ 0<N) y≤tk)) Ntk<tn)

-- classical logic at `Set` from classical logic at `Set₁`
lemOf : LEM₁ → LEM₀
lemOf lem₁ P with lem₁ (Lift (L.suc L.zero) P)
... | inj₁ (lift p) = inj₁ p
... | inj₂ n = inj₂ (λ p → n (lift p))

-- the Daniell integral of the Borel measure `B`
module DaniellB (lem₁ : LEM₁) (B : BM.BorelMeasure (lemOf lem₁)) where

  open Simple (lemOf lem₁) B
  open Sf
  open OmegaSemiring A renaming (Carrier to ∣A∣; zero to zero-sr)
  open Series A
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring using (solve; _:+_; _:*_; _:=_; con)
  open Grid (lemOf lem₁) B
  open Cont (lemOf lem₁) B
  open BM.BorelMeasure B using (μ; μ-resp)
  open SeriesSup.SeriesSup A
  open LevelSets (lemOf lem₁) using (Lvl)

  private
    dec : Set₁ → Bool
    dec P with lem₁ P
    ... | inj₁ _ = true
    ... | inj₂ _ = false

    dec-true : ∀ {P} → P → dec P ≡ true
    dec-true {P} p with lem₁ P
    ... | inj₁ _ = ≡.refl
    ... | inj₂ np = ⊥-elim (np p)

    from-true : ∀ {P} → dec P ≡ true → P
    from-true {P} e with lem₁ P
    ... | inj₁ p = p

  -- s lies below h
  Minor : (R₁ → Cut) → Sf → Set₁
  Minor h s = ∀ i x → V s i x → ρ s i ⊑ h (lift x)

  Lmem : (R₁ → Cut) → ℚᵘ → Set₁
  Lmem h q = Σ Sf (λ s → Minor h s × mem (∫ s) q)

  -- the integral of h: the supremum of the integrals of the simple functions below it
  L : (R₁ → Cut) → Cut
  L h = record
    { mem = λ q → q < 0ℚᵘ ⊎ (dec (Lmem h q) ≡ true)
    ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt)
               ; le (inj₂ e) → let s , mn , m = from-true e in inj₂ (dec-true (s , mn , down (∫ s) le m)) }
    ; open′ = λ { (inj₁ lt) → let r , a , b = dense lt in r , a , inj₁ b
                ; (inj₂ e) → let s , mn , m = from-true e
                                 r , a , m′ = open′ (∫ s) m
                             in r , a , inj₂ (dec-true (s , mn , m′)) }
    ; neg = inj₁ }

  L-ub : ∀ {h s} → Minor h s → ∫ s ≤ L h
  L-ub {h} {s} mn = mk⊑ (λ q m → inj₂ (dec-true (s , mn , m)))

  L-lub : ∀ {h b} → (∀ s → Minor h s → ∫ s ≤ b) → L h ≤ b
  L-lub {h} {b} H = mk⊑ (λ { q (inj₁ lt) → neg b lt
                           ; q (inj₂ e) → let s , mn , m = from-true e in ap (H s mn) q m })

  L-mono : ∀ {h h′} → (∀ x → h x ≤ h′ x) → L h ≤ L h′
  L-mono {h} {h′} le = L-lub {h} {L h′} (λ s mn → L-ub {h′} {s} (λ i x v → ≤-trans (mn i x v) (le (lift x))))

  L-cong : ∀ {h h′} → (∀ x → h x ≈ h′ x) → L h ≈ L h′
  L-cong e = ≤-antisym (L-mono (λ x → ≤-reflexive (e x))) (L-mono (λ x → ≤-reflexive (sym (e x))))

  -- every element of the integral lies below the integral of some minorant (0 is one)
  L-elt : ∀ {h q} → mem (L h) q → Σ Sf (λ s → Minor h s × mem (∫ s) q)
  L-elt {h} {q} (inj₁ lt) = sconst 0# , (λ i x v → 0-least) , ap (proj₂ (∫-sconst 0#)) q lt
  L-elt {h} {q} (inj₂ e) = from-true e

  ----------------------------------------------------------------------------
  -- normalisation

  L-one : L (λ _ → 1#) ≈ 1#
  L-one = ≤-antisym
    (L-lub (λ s mn → ≤-trans (∫-mono s (sconst 1#) (λ i j x vi vj → mn i x vi)) (≤-reflexive (∫-sconst 1#))))
    (≤-trans (≤-reflexive (sym (∫-sconst 1#))) (L-ub {λ _ → 1#} {sconst 1#} (λ i x v → ≤-refl)))

  ----------------------------------------------------------------------------
  -- additivity

  ⊕-lub : ∀ {h₁ h₂ b} → (∀ s₁ s₂ → Minor h₁ s₁ → Minor h₂ s₂ → ∫ s₁ + ∫ s₂ ≤ b) → L h₁ + L h₂ ≤ b
  ⊕-lub {h₁} {h₂} {b} H = mk⊑ λ { q (r , t , mr , mt , le) →
    let s₁ , mn₁ , m₁ = L-elt {h₁} mr
        s₂ , mn₂ , m₂ = L-elt {h₂} mt
    in ap (H s₁ s₂ mn₁ mn₂) q (r , t , m₁ , m₂ , le) }

  rC-hp : ∀ m → rC (tp m) ≤ hpC m
  rC-hp m = mk⊑ λ { s (inj₁ lt) → lt ; s (inj₂ lt) → RL.<-trans lt (tp-pos m) }

  module Add {h h₁ h₂ : R₁ → Cut} (e : ∀ x → h x ≈ h₁ x + h₂ x)
             (LV₁ : ∀ q → Borel (Lvl h₁ q)) (LV₂ : ∀ q → Borel (Lvl h₂ q))
             (bd₁ : ∀ x → h₁ x ≤ 1#) (bd₂ : ∀ x → h₂ x ≤ 1#) where

    minor : ∀ s₁ s₂ → Minor h₁ s₁ → Minor h₂ s₂ → Minor h (sadd s₁ s₂)
    minor s₁ s₂ mn₁ mn₂ k x (a , b) = ≤-trans (+-mono (mn₁ _ x a) (mn₂ _ x b)) (≤-reflexive (sym (e (lift x))))

    add≥ : L h₁ + L h₂ ≤ L h
    add≥ = ⊕-lub (λ s₁ s₂ mn₁ mn₂ →
      ≤-trans (≤-reflexive (sym (∫-sadd s₁ s₂))) (L-ub {h} {sadd s₁ s₂} (minor s₁ s₂ mn₁ mn₂)))

    -- the integral of a minorant is within 2⁻ⁿ of the integrals of the summands
    bound : ∀ n s → Minor h s → ∫ s ≤ (L h₁ + L h₂) + hpC n
    bound n s mn = ≤-trans (∫-mono s t hyp)
      (≤-trans (≤-reflexive ∫t) (+-mono-both))
      where
        k = suc n
        g₁ = grid k h₁ LV₁ bd₁
        g₂ = grid k h₂ LV₂ bd₂
        τ = rC (tp k) + rC (tp k)
        t = sadd (sadd g₁ g₂) (sconst τ)
        ∫t : ∫ t ≈ (∫ g₁ + ∫ g₂) + τ
        ∫t = trans (∫-sadd (sadd g₁ g₂) (sconst τ)) (+-cong (∫-sadd g₁ g₂) (∫-sconst τ))
        τ≤ : τ ≤ hpC n
        τ≤ = ≤-trans (+-mono (rC-hp k) (rC-hp k)) (proj₁ (hpC-double n))
        +-mono-both : (∫ g₁ + ∫ g₂) + τ ≤ (L h₁ + L h₂) + hpC n
        +-mono-both = +-mono (+-mono (L-ub {h₁} {g₁} (λ i x v → grid-minor k h₁ LV₁ bd₁ i x v))
                                     (L-ub {h₂} {g₂} (λ i x v → grid-minor k h₂ LV₂ bd₂ i x v))) τ≤
        hyp : ∀ i j x → V s i x → V t j x → ρ s i ≤ ρ t j
        hyp i j x vi ((ga , gb) , _) = ≤-trans (mn i x vi) (≤-trans (≤-reflexive (e (lift x)))
          (≤-trans (+-mono (grid-upper k h₁ LV₁ bd₁ _ x ga) (grid-upper k h₂ LV₂ bd₂ _ x gb))
            (≤-trans (+-mono (rC-th-suc k _) (rC-th-suc k _))
              (≤-reflexive (solve 4 (λ p q u v → (p :+ q) :+ (u :+ v) := (p :+ u) :+ (q :+ v)) refl
                                  (rC (th k _)) (rC (tp k)) (rC (th k _)) (rC (tp k)))))))

    add≤ : L h ≤ L h₁ + L h₂
    add≤ = L-lub (λ s mn → arch-⊑ (lemOf lem₁) (λ n → bound n s mn))

    L-add : L h ≈ L h₁ + L h₂
    L-add = ≤-antisym add≤ add≥
  ----------------------------------------------------------------------------
  -- scaling

  module Scale {h h′ : R₁ → Cut} (c : ∣A∣) (e : ∀ x → h′ x ≈ c * h x) where

    scale≥ : c * L h ≤ L h′
    scale≥ = mk⊑ λ { q (inj₁ lt) → neg (L h′) lt
                   ; q (inj₂ (r , t , 0<r , 0<t , mr , mt , le)) →
                       let r″ , r<r″ , mr″ = open′ c mr
                           s , mn , m = L-elt {h} mt
                           rr = rC r″
                           rr≤c : rr ≤ c
                           rr≤c = mk⊑ λ { s′ (inj₁ lt′) → down c (RL.<-≤ lt′) mr″ ; s′ (inj₂ lt′) → neg c lt′ }
                           minor : Minor h′ (sscale rr s)
                           minor i x v = ≤-trans (⊗-mono rr≤c (mn i x v)) (≤-reflexive (sym (e (lift x))))
                           inprod : mem (rr * ∫ s) q
                           inprod = inj₂ (r , t , 0<r , 0<t , inj₁ r<r″ , m , le)
                       in ap (≤-trans (proj₂ (∫-sscale rr s)) (L-ub {h′} {sscale rr s} minor)) q inprod }


    -- c below a rational N: the grid argument
    module Fin (LV : ∀ q → Borel (Lvl h q)) (bd : ∀ x → h x ≤ 1#)
               (N : ℚᵘ) (0<N : 0ℚᵘ < N) (cN : c ≤ rC N) where
      ν : ℚᵘ
      ν = proj₁ (RL.inv 0<N)

      νN : ν *ᵘ N ≃ᵘ 1ℚᵘ
      νN = proj₂ (RL.inv 0<N)

      0<ν : 0ℚᵘ < ν
      0<ν with RL.pos-or-nonpos ν
      ... | inj₁ p = p
      ... | inj₂ np = ⊥-elim (RL.<-irrefl RL.≃-refl (RL.<-≤-trans RL.0<1
          (RL.≤-resp νN (RL.*-zeroˡ N) (RL.*-mono-≤-nnʳ (RL.<-≤ 0<N) np))))

      below : ∀ (r : ℚᵘ) → 0ℚᵘ < r → mem (rC N) r → r < N
      below r 0<r (inj₁ lt) = lt
      below r 0<r (inj₂ lt) = ⊥-elim (RL.<-irrefl RL.≃-refl (RL.<-trans 0<r lt))

      below′ : ∀ (k : ℕ) (y : ℚᵘ) → 0ℚᵘ < y → mem (rC (tp k)) y → y < tp k
      below′ k y 0<y (inj₁ lt) = lt
      below′ k y 0<y (inj₂ lt) = ⊥-elim (RL.<-irrefl RL.≃-refl (RL.<-trans 0<y lt))

      Ntk : ∀ n (k : ℕ) → tp k < ν *ᵘ tp n → N *ᵘ tp k < tp n
      Ntk n k tk<δ = RL.≃-<ʳ (RL.≃-trans (RL.≃-sym (RL.*-assoc N ν (tp n)))
                               (RL.≃-trans (RL.*-cong (RL.*-comm N ν) RL.≃-refl)
                                 (RL.≃-trans (RL.*-cong νN RL.≃-refl) (RL.*-identityˡ (tp n)))))
                            (RL.*-mono-<-pos 0<N tk<δ)

      tol-le : ∀ n (k : ℕ) → tp k < ν *ᵘ tp n → c * rC (tp k) ≤ hpC n
      tol-le n k tk<δ = mk⊑ go
        where
          go : ∀ q → mem (c * rC (tp k)) q → q < tp n
          go q (inj₁ lt) = RL.<-trans lt (tp-pos n)
          go q (inj₂ (r , y , 0<r , 0<y , mr , my , le)) =
            smallprod {N} {tp k} {tp n} {r} {y} {q} 0<N 0<y (below r 0<r (ap cN r mr))
              (RL.<-≤ (below′ k y 0<y my)) (Ntk n k tk<δ) le

      tol : ∀ n → Σ ℕ (λ k → c * rC (tp k) ≤ hpC n)
      tol n with tp-small (ν *ᵘ tp n) (RL.*-pos 0<ν (tp-pos n))
      ... | k , tk<δ = k , tol-le n k tk<δ

      -- a point of the a-th grid cell
      cellbound : ∀ (k : ℕ) (x : Cantor) (a : ℕ) → gcell k h LV bd a x →
        h′ (lift x) ≤ c * rC (th k a) + c * rC (tp k)
      cellbound k x a ga = ≤-trans (≤-reflexive (e (lift x)))
        (≤-trans (*-mono c (grid-upper k h LV bd a x ga))
          (≤-trans (*-mono c (rC-th-suc k a))
            (≤-reflexive (distribˡ c (rC (th k a)) (rC (tp k))))))

      bound-at : ∀ n k → c * rC (tp k) ≤ hpC n → ∀ s → Minor h′ s → ∫ s ≤ c * L h + hpC n
      bound-at n k tolk s mn = ≤-trans (∫-mono s t hyp) (≤-trans (≤-reflexive ∫t) fin)
        where
          g : Sf
          g = grid k h LV bd
          t : Sf
          t = sadd (sscale c g) (sconst (c * rC (tp k)))
          ∫t : ∫ t ≈ c * ∫ g + c * rC (tp k)
          ∫t = trans (∫-sadd (sscale c g) (sconst (c * rC (tp k)))) (+-cong (∫-sscale c g) (∫-sconst (c * rC (tp k))))
          g≤ : ∫ g ≤ L h
          g≤ = L-ub {h} {g} (λ i x v → grid-minor k h LV bd i x v)
          fin : c * ∫ g + c * rC (tp k) ≤ c * L h + hpC n
          fin = +-mono (*-mono c g≤) tolk
          hyp : ∀ i j x → V s i x → V t j x → ρ s i ≤ ρ t j
          hyp i j x vi (ga , _) = ≤-trans (mn i x vi) (cellbound k x (proj₁ (unpair j)) ga)

      bound : ∀ n s → Minor h′ s → ∫ s ≤ c * L h + hpC n
      bound n s mn = bound-at n (proj₁ (tol n)) (proj₂ (tol n)) s mn

      scale≤ : L h′ ≤ c * L h
      scale≤ = L-lub {h′} {c * L h} (λ s mn → arch-⊑ (lemOf lem₁) {∫ s} {c * L h} (λ n → bound n s mn))

    -- c above every rational: h must vanish
    module Inf (bd′ : ∀ x → h′ x ≤ 1#) (allc : ∀ q → mem c q) where
      nat-pos : ∀ k → 0ℚᵘ < RL.nat (suc k)
      nat-pos k = RL.≃-<ʳ (RL.≃-sym (RL.nat-suc k))
        (RL.≃-<ˡ (RL.+-identityˡ 0ℚᵘ) (RL.+-mono-≤-< (nat-nonneg k) RL.0<1))

      clash′ : ∀ (x : R₁) (q′ : ℚᵘ) → 0ℚᵘ < q′ → mem (h x) q′ → ∀ (k : ℕ) → 1ℚᵘ ≤ᵘ RL.nat k *ᵘ q′ → ⊥
      clash′ x q′ 0<q′ m′ k 1≤ = RL.<-irrefl RL.≃-refl (ap (bd′ x) 1ℚᵘ (ap (proj₂ (e x)) 1ℚᵘ (inj₂ w)))
        where
          le1 : 1ℚᵘ ≤ᵘ RL.nat (suc k) *ᵘ q′
          le1 = RL.≤-trans 1≤
              (RL.*-mono-≤-nnʳ (RL.<-≤ 0<q′) (RL.nat-mono (ℕₚ.n≤1+n k)))
          w : Σ ℚᵘ (λ r → Σ ℚᵘ (λ t → 0ℚᵘ < r × 0ℚᵘ < t × mem c r × mem (h x) t × 1ℚᵘ ≤ᵘ r *ᵘ t))
          w = RL.nat (suc k) , q′ , nat-pos k , 0<q′ , allc (RL.nat (suc k)) , m′ , le1

      clash : ∀ (x : R₁) (q′ : ℚᵘ) → 0ℚᵘ < q′ → mem (h x) q′ → ⊥
      clash x q′ 0<q′ m′ = clash′ x q′ 0<q′ m′ (proj₁ (RL.arch 1ℚᵘ {q′} 0<q′)) (proj₂ (RL.arch 1ℚᵘ {q′} 0<q′))

      nonpos : ∀ x q → mem (h x) q → (q < 0ℚᵘ ⊎ 0ℚᵘ ≤ᵘ q) → mem 0# q
      nonpos x q m (inj₁ lt) = lt
      nonpos x q m (inj₂ 0≤q) = ⊥-elim
          (clash x (proj₁ (open′ (h x) m)) (RL.≤-<-trans 0≤q (proj₁ (proj₂ (open′ (h x) m)))) (proj₂ (proj₂ (open′ (h x) m))))

      zeroh : ∀ x → h x ≤ 0#
      zeroh x = mk⊑ λ q m → nonpos x q m (RL.neg-or-nonneg q)

      z′ : ∀ x → h′ x ≤ 0#
      z′ x = ≤-trans (≤-reflexive (e x)) (≤-trans (*-mono c (zeroh x)) (≤-reflexive (zeroʳ c)))

      L≤0 : L h′ ≤ 0#
      L≤0 = L-lub {h′} {0#} (λ s mn → ≤-trans (∫-mono s (sconst 0#) (λ i j x vi vj → ≤-trans (mn i x vi) (z′ (lift x))))
                                           (≤-reflexive (∫-sconst 0#)))

      scale≤ : L h′ ≤ c * L h
      scale≤ = ≤-trans L≤0 0-least

    cle : ∀ (q0 N : ℚᵘ) → 0ℚᵘ < N → q0 ≤ᵘ N → (mem c q0 → ⊥) → c ≤ rC N
    cle q0 N 0<N q0≤N nm = mk⊑ λ s m → inj₁ (go s m (RL.≤-or-> N s))
      where
        go : ∀ s → mem c s → (N ≤ᵘ s ⊎ s < N) → s < N
        go s m (inj₁ N≤s) = ⊥-elim (nm (down c (RL.≤-trans q0≤N N≤s) m))
        go s m (inj₂ lt) = lt

    scale≤-fin : (LV : ∀ q → Borel (Lvl h q)) (bd : ∀ x → h x ≤ 1#) (q0 : ℚᵘ) → (mem c q0 → ⊥) →
      (q0 ≤ᵘ 1ℚᵘ ⊎ 1ℚᵘ < q0) → L h′ ≤ c * L h
    scale≤-fin LV bd q0 nm (inj₁ le) = Fin.scale≤ LV bd 1ℚᵘ RL.0<1 (cle q0 1ℚᵘ RL.0<1 le nm)
    scale≤-fin LV bd q0 nm (inj₂ lt) = Fin.scale≤ LV bd q0 (RL.<-trans RL.0<1 lt) (cle q0 q0 (RL.<-trans RL.0<1 lt) RL.≤-refl nm)

    allc-from : (∀ k → mem c (enumQ k)) → ∀ q → mem c q
    allc-from all q = ≡.subst (mem c) (proj₂ (enumQ-surj q)) (all (proj₁ (enumQ-surj q)))

    memk : ∀ (k : ℕ) → (Σ ℕ (λ k → mem c (enumQ k) → ⊥) → ⊥) → (mem c (enumQ k) ⊎ (mem c (enumQ k) → ⊥)) → mem c (enumQ k)
    memk k nn (inj₁ m) = m
    memk k nn (inj₂ nm) = ⊥-elim (nn (k , nm))

    scale≤-dec : (LV : ∀ q → Borel (Lvl h q)) (bd : ∀ x → h x ≤ 1#) (bd′ : ∀ x → h′ x ≤ 1#) →
      (Σ ℕ (λ k → mem c (enumQ k) → ⊥) ⊎ (Σ ℕ (λ k → mem c (enumQ k) → ⊥) → ⊥)) → L h′ ≤ c * L h
    scale≤-dec LV bd bd′ (inj₁ (k , nm)) = scale≤-fin LV bd (enumQ k) nm (RL.≤-or-> (enumQ k) 1ℚᵘ)
    scale≤-dec LV bd bd′ (inj₂ nn) = Inf.scale≤ bd′ (allc-from (λ k → memk k nn ((lemOf lem₁) (mem c (enumQ k)))))

    L-scale : (LV : ∀ q → Borel (Lvl h q)) (bd : ∀ x → h x ≤ 1#) (bd′ : ∀ x → h′ x ≤ 1#) → L h′ ≈ c * L h
    L-scale LV bd bd′ = ≤-antisym (scale≤-dec LV bd bd′ ((lemOf lem₁) (Σ ℕ (λ k → mem c (enumQ k) → ⊥)))) scale≥

  ----------------------------------------------------------------------------
  -- monotone convergence

  rC-zero : rC 0ℚᵘ ≈ 0#
  rC-zero = mk⊑ (λ { s (inj₁ lt) → lt ; s (inj₂ lt) → lt }) , mk⊑ (λ s lt → inj₁ lt)

  incL′ : (hs : ℕ → R₁ → Cut) → (∀ x → Increasing (λ n → hs n x)) → Increasing (λ n → L (hs n))
  incL′ hs inc n = L-mono {hs n} {hs (suc n)} (λ x → inc x n)

  module Sup {h : R₁ → Cut} (hs : ℕ → R₁ → Cut) (inc : ∀ x → Increasing (λ n → hs n x))
             (e : ∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x))
             (LV : ∀ q → Borel (Lvl h q)) (LVs : ∀ n q → Borel (Lvl (hs n) q)) (bd : ∀ x → h x ≤ 1#) (k : ℕ) where

    g : Sf
    g = grid k h LV bd

    -- the part of the a-th grid cell where hs n already exceeds the a-th grid point
    Wc : ℕ → ℕ → Pred
    Wc a n c = gcell k h LV bd a c × mem (hs n (lift c)) (th k a)

    bWc : ∀ a n → Borel (Wc a n)
    bWc a n = inter₂ (gB k h LV bd a) (LVs n (th k a))

    Wsub : ∀ a n x → Wc a n x → Wc a (suc n) x
    Wsub a n x (gc , m) = gc , ap (inc (lift x) n) (th k a) m

    Wdj : ∀ n → Disjoint (λ a → Wc a n)
    Wdj n x a b (ga , _) (gb , _) = g-dj k h LV bd x a b ga gb

    -- for a ≥ 1 the cells exhaust the grid cell
    Wunion : ∀ a → (λ x → Σ ℕ (λ n → Wc (suc a) n x)) ≐ gcell k h LV bd (suc a)
    Wunion a x = (λ { (n , gc , _) → gc })
               , (λ gc → let t = gcell-T k h LV bd a x gc
                             n , m = ap (proj₁ (e (lift x))) (th k (suc a)) t
                         in n , gc , m)

    incW : ∀ a → Increasing (λ n → rC (th k a) * μ (bWc a n))
    incW a n = *-mono (rC (th k a)) (μ-mono (bWc a n) (bWc a (suc n)) (Wsub a n))

    term≤ : ∀ a → rC (th k a) * μ (gB k h LV bd a) ≤ ⨆ (λ n → rC (th k a) * μ (bWc a n)) (incW a)
    term≤ zero = ≤-trans (≤-reflexive (trans (*-cong (rC-cong-zero) refl) (zeroˡ _))) 0-least
      where rC-cong-zero : rC (th k 0) ≈ 0#
            rC-cong-zero = trans (rC-cong (th-zero k)) rC-zero
    term≤ (suc a) = ≤-trans (≤-reflexive (trans (*-cong refl m≈) (*-⨆ (rC (th k (suc a))) (λ n → μ (bWc (suc a) n))
                                                       (λ n → μ-mono (bWc (suc a) n) (bWc (suc a) (suc n))
                                                           (Wsub (suc a) n)) (incW (suc a)))))
                            ≤-refl
      where
        m≈ : μ (gB k h LV bd (suc a)) ≈ ⨆ (λ n → μ (bWc (suc a) n))
            (λ n → μ-mono (bWc (suc a) n) (bWc (suc a) (suc n)) (Wsub (suc a) n))
        m≈ = trans (μ-resp (gB k h LV bd (suc a)) (⋃ (bWc (suc a))) (λ x → proj₂ (Wunion a x) , proj₁ (Wunion a x)))
                   (μ-cont (Wc (suc a)) (bWc (suc a)) (Wsub (suc a)))

    sn : ℕ → Sf
    sn n = complete (λ a → Wc a n) (λ a → bWc a n) (Wdj n) (λ a → rC (th k a))

    sn-minor : ∀ n → Minor (hs n) (sn n)
    sn-minor n zero x v = 0-least
    sn-minor n (suc a) x (gc , m) = mk⊑ λ { s (inj₁ lt) → down (hs n (lift x)) (RL.<-≤ lt) m
                                          ; s (inj₂ lt) → neg (hs n (lift x)) lt }

    ∫sn≤ : ∀ n → ∑ᶠ (λ a → rC (th k a) * μ (bWc a n)) ≤ L (hs n)
    ∫sn≤ n = ≤-trans (≤-reflexive (sym (∫-complete (λ a → Wc a n) (λ a → bWc a n) (Wdj n) (λ a → rC (th k a)))))
                     (L-ub {hs n} {sn n} (sn-minor n))

    incL : Increasing (λ n → L (hs n))
    incL = incL′ hs inc

    mct : ∫ g ≤ ⨆ (λ n → L (hs n)) incL
    mct = ≤-trans (∑ᶠ-mono term≤)
      (≤-trans (≤-reflexive (∑ᶠ-⨆ (λ a n → rC (th k a) * μ (bWc a n)) incW))
               (⨆-mono (λ n → ∑ᶠ-mono (λ a → incW a n)) incL ∫sn≤))

  module SupLaw {h : R₁ → Cut} (hs : ℕ → R₁ → Cut) (inc : ∀ x → Increasing (λ n → hs n x))
                (e : ∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x))
                (LV : ∀ q → Borel (Lvl h q)) (LVs : ∀ n q → Borel (Lvl (hs n) q)) (bd : ∀ x → h x ≤ 1#) where

    sup≥ : ⨆ (λ n → L (hs n)) (incL′ hs inc) ≤ L h
    sup≥ = ⨆-lub (λ n → L (hs n)) (incL′ hs inc)
      (λ n → L-mono {hs n} {h} (λ x → ≤-trans (⨆-ub (λ m → hs m x) (inc x) n) (≤-reflexive (sym (e x)))))

    cellsup : ∀ (k : ℕ) (x : Cantor) (a : ℕ) → gcell k h LV bd a x →
      h (lift x) ≤ rC (th k a) + rC (tp k)
    cellsup k x a ga = ≤-trans (grid-upper k h LV bd a x ga) (rC-th-suc k a)

    bound-sup : ∀ n s → Minor h s → ∫ s ≤ ⨆ (λ m → L (hs m)) (incL′ hs inc) + hpC n
    bound-sup n s mn = ≤-trans (∫-mono s t hyp) (≤-trans (≤-reflexive ∫t) (+-mono (Sup.mct hs inc e LV LVs bd (suc n)) τ≤))
      where
        k = suc n
        t : Sf
        t = sadd (grid k h LV bd) (sconst (rC (tp k)))
        ∫t : ∫ t ≈ ∫ (grid k h LV bd) + rC (tp k)
        ∫t = trans (∫-sadd (grid k h LV bd) (sconst (rC (tp k)))) (+-cong (refl {∫ (grid k h LV bd)}) (∫-sconst (rC (tp k))))
        τ≤ : rC (tp k) ≤ hpC n
        τ≤ = ≤-trans (rC-hp k) (≤-trans (≤-+ʳ {hpC (suc n)} {hpC (suc n)}) (proj₁ (hpC-double n)))
        hyp : ∀ i j x → V s i x → V t j x → ρ s i ≤ ρ t j
        hyp i j x vi (ga , _) = ≤-trans (mn i x vi) (cellsup k x (proj₁ (unpair j)) ga)

    sup≤ : L h ≤ ⨆ (λ n → L (hs n)) (incL′ hs inc)
    sup≤ = L-lub {h} {⨆ (λ n → L (hs n)) (incL′ hs inc)}
      (λ s mn → arch-⊑ (lemOf lem₁) {∫ s} {⨆ (λ n → L (hs n)) (incL′ hs inc)} (λ n → bound-sup n s mn))

    L-sup : L h ≈ ⨆ (λ n → L (hs n)) (incL′ hs inc)
    L-sup = ≤-antisym sup≤ sup≥

-- the fair coin
module Daniell (lem₁ : LEM₁) = DaniellB lem₁ (BM.coinBM (lemOf lem₁))
