{-# OPTIONS --safe --without-K #-}

-- Facts about +∞ in [0, ∞] used by the signed layer.
--   * `not-bnd-top`: a value with no natural bound is ∞;  `∞-abs`: ∞ + b ≈ ∞;
--   * `cancel-bnd` (re-exported from `BoundedCancel` for `lemOf lem₁`);
--   * `top-sum`, `top-ge`, `sum-top-bnd`, `top-left`, `top-right-le`: ∞ absorbs sums and bounds everything, and a sum
--     p + n′ + k with n′, k bounded equal to (or above) ∞ has p equal to ∞;
--   * `bnd-top-⊥`: ∞ is not bounded;  `fin-sum-⊥`: x + a ≈ ∞ with a bounded forces x unbounded.
-- Route: `MonusAlg.cut-total` against `nat n` (excluded middle), with `ExpLower.natE≋` for membership in `nat n`;
-- `bnd-rat` for the rational bound of a bounded value.
module QBS.Continuous.InfAlg where

open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (suc)
open import Data.Unit.Base using (tt)
open import Data.Rational.Unnormalised.Base using () renaming (_<_ to _<ℚ_; _≤_ to _≤ℚ_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (Cut; module Cut; _⊑_; mk⊑; module _⊑_; infC)
open import QBS.Analysis.ExpLower using (natE≋)
open import QBS.Analysis.RationalLemmas using (≃-sym; ≃-<ʳ; lt-add; 0<1; nat-suc; nat-bound; ≤-<-trans; <-irrefl; ≃-refl)
  renaming (nat to natℚ)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Continuous.MonusAlg using (module MonusAlg)

open Cut using (mem)
open _⊑_ using (ap)

-- ∞ times a nonzero value is ∞ in [0, ∞] (used by `SignedMul`).
--   * `ex-pos`: a cut that is not 0 has a positive member (excluded middle on the rationals);
--   * `top-pos`: infC ⊗ y ≋ infC when y ≉ 0.
-- Route: take a positive s ∈ y; for a rational q the Archimedean property gives q ≤ k s, and r = k + 1 > 0 has
-- q ≤ r s, so q lies in infC ⊗ y.
module TopMulPos where
  open import Data.Product.Base using (Σ; _×_)
  open import Data.Unit.Base using (tt)
  open import QBS.Classical using (LEM₀)
  open import QBS.Analysis.RationalLemmas
  open import QBS.Analysis.LowerReals using (zeroC; _≋_; _⊗_; 0-least)

  open Cut using (open′)

  -- a nonzero cut has a positive member
  ex-pos : LEM₀ → ∀ y → (y ≋ zeroC → ⊥) → Σ ℚᵘ (λ s → 0ℚᵘ <ᵘ s × mem y s)
  ex-pos lem y nz with lem (Σ ℚᵘ (λ s → mem y s × 0ℚᵘ ≤ᵘ s))
  ... | inj₁ (s , ms , 0≤s) with open′ y ms
  ...   | s′ , s<s′ , ms′ = s′ , ≤-<-trans 0≤s s<s′ , ms′
  ex-pos lem y nz | inj₂ no = ⊥-elim (nz (mk⊑ fwd , 0-least))
    where
      fwd : ∀ q → mem y q → q <ᵘ 0ℚᵘ
      fwd q mq with neg-or-nonneg q
      ... | inj₁ q<0 = q<0
      ... | inj₂ 0≤q = ⊥-elim (no (q , mq , 0≤q))

  top-pos : LEM₀ → ∀ y → (y ≋ zeroC → ⊥) → infC ⊗ y ≋ infC
  top-pos lem y nz = mk⊑ (λ _ _ → tt) , mk⊑ (λ q _ → body q)
    where
      s = proj₁ (ex-pos lem y nz)
      0<s = proj₁ (proj₂ (ex-pos lem y nz))
      ms = proj₂ (proj₂ (ex-pos lem y nz))
      body : ∀ q → mem (infC ⊗ y) q
      body q with arch q 0<s
      ... | k , qk = inj₂ (nat (suc k) , s ,
        ≤-<-trans (nat-nonneg k) (≃-<ʳ (≃-sym (nat-suc k)) (lt-add 0<1)) , 0<s , tt , ms ,
        ≤-trans qk (≤-trans (≤-trans (≤-≃ (≃-sym (+-identityʳ _))) (+-mono-≤ (≤-refl {_}) (<-≤ 0<s)))
          (≤-≃ (≃-sym (nat-suc* k s)))))

module InfAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; ≤-trans; ≤-reflexive; ≤-+ʳ; +-comm; +-cong; ≤-antisym; trans; sym)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat; finite)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open BoundedCancel A half hh public using (cancel-bnd)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat)
  open LebesgueShiftAlg (lemOf lem₁) using (bnd-rat)
  open MonusAlg lem₁ using (cut-total)

  -- every rational below n is in `nat n`
  nat-mem : ∀ k r → r <ℚ natℚ (suc k) → mem (nat (suc k)) r
  nat-mem k r lt = ap (≤-reflexive (natE≈nat (suc k))) r (ap (proj₂ (natE≋ (lemOf lem₁) k)) r lt)

  top-⊑ : ∀ {a : ∣A∣} → infC ≤ a → a ≈ infC
  top-⊑ {a} h = ≤-antisym {a} {infC} (mk⊑ (λ _ _ → tt)) h

  above-case : ∀ a q k → q ≤ℚ natℚ k → (Bnd a → ⊥) → a ≤ nat (suc k) ⊎ nat (suc k) ≤ a → mem a q
  above-case a q k qk nb (inj₁ le) = ⊥-elim (nb (suc k , le))
  above-case a q k qk nb (inj₂ ge) =
    ap ge q (nat-mem k q (≤-<-trans qk (≃-<ʳ (≃-sym (nat-suc k)) (lt-add 0<1))))

  above : ∀ a q → (Bnd a → ⊥) → mem a q
  above a q nb = above-case a q (proj₁ (nat-bound q)) (proj₂ (nat-bound q)) nb (cut-total a (nat (suc (proj₁ (nat-bound q)))))

  not-bnd-top : ∀ a → (Bnd a → ⊥) → a ≈ infC
  not-bnd-top a nb = top-⊑ {a} (mk⊑ (λ q _ → above a q nb))

  ∞-abs : ∀ b → infC + b ≈ infC
  ∞-abs b = ≤-antisym {infC + b} {infC} (mk⊑ (λ _ _ → tt)) (≤-+ʳ {infC} {b})

  bnd-top-⊥ : Bnd infC → ⊥
  bnd-top-⊥ bd = <-irrefl ≃-refl (proj₂ (bnd-rat infC bd) (proj₁ (bnd-rat infC bd)) tt)

  fin-sum-⊥ : ∀ {x a} → Bnd a → x + a ≈ infC → Bnd x → ⊥
  fin-sum-⊥ {x} {a} ba e bx = bnd-top-⊥ (Is-resp {x + a} {infC} e (Is-+ {x} {a} bx ba))
    where open import QBS.Analysis.Signed using (SubSemiring); open SubSemiring finite

  top-sum : ∀ {p} → p ≈ infC → ∀ b → p + b ≈ infC
  top-sum h b = trans (+-cong h (OmegaSemiring.refl A)) (∞-abs b)

  top-ge : ∀ {x} → x ≈ infC → ∀ y → y ≤ x
  top-ge {x} h y = ≤-trans (mk⊑ (λ _ _ → tt)) (≤-reflexive (sym h))

  sum-top-bnd : ∀ {x a} → Bnd a → x + a ≈ infC → x ≈ infC
  sum-top-bnd {x} ba e = not-bnd-top x (fin-sum-⊥ ba e)

  -- p + n′ + k ≈ p′ + n + k with p′ = ∞ and n′, k bounded gives p = ∞
  top-left : ∀ {p p′ n n′ k} → Bnd n′ → Bnd k → p′ ≈ infC → p + n′ + k ≈ p′ + n + k → p ≈ infC
  top-left {p} {n′ = n′} {k} bn′ bk h e =
    sum-top-bnd {p} {n′} bn′ (sum-top-bnd {p + n′} {k} bk (trans e (top-sum (top-sum h _) _)))

  -- the same for `≤`: ∞ ≈ p′ + n″ + k ≤ p″ + n′ + k gives p″ = ∞
  top-right-le : ∀ {p′ p″ n′ n″ k} → Bnd n′ → Bnd k → p′ ≈ infC → p′ + n″ + k ≤ p″ + n′ + k → p″ ≈ infC
  top-right-le {p″ = p″} {n′} {n″} {k} bn′ bk h le =
    sum-top-bnd {p″} {n′} bn′ (sum-top-bnd {p″ + n′} {k} bk
      (top-⊑ {p″ + n′ + k} (≤-trans (≤-reflexive (sym (top-sum (top-sum h n″) k))) le)))
