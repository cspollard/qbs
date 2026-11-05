{-# OPTIONS --safe --without-K #-}

-- Algebra of rationally bounded lower reals and truncated subtraction (plan 03, "Signed dominated convergence").
--   * `BndQ-≤`, `BndQ-≈`, `BndQ-add`, `BndQ-0`, `rat-bnd`: rational bounds are downward closed, respect ≈, add, and
--     give a natural-number bound (`Bounded.Bnd`);
--   * `cut-total`: any two lower reals are comparable (excluded middle on a rational in one but not the other);
--   * `monus-le`: x ∸ t ≤ x;  `monus-small`: d ≤ e + ε with e bounded gives d ∸ e ≤ ε;
--     `monus-swap`: d + (e ∸ d) ≈ e + (d ∸ e) for bounded d, e.
-- Route: `cut-total` by a case split on a rational q ∈ b with q ∉ a; the monus facts from `Monus.monus-add`
-- (for t ≤ x) and `Monus.monus-zero` (for x ≤ t) in each case of `cut-total`, with `LowerRealsNear.cancel-bnd-⊑`;
-- `rat-bnd` from `natE (n+1) ≋ n+1` (`ExpLower.natE≋`).
module QBS.Continuous.MonusAlg where

open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (suc)
open import Data.Rational.Unnormalised.Base using () renaming (_+_ to _+ℚ_; _<_ to _<ℚ_)
import Data.Rational.Unnormalised.Properties as ℚP

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (Cut; module Cut; _⊑_; mk⊑; module _⊑_)
open import QBS.Analysis.LowerRealsNear using (BndQ; module Near)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.ExpLower using (natE≋)
open import QBS.Analysis.RationalLemmas using (ℚᵘ; ≤-or->; <-≤; <-trans; ≤-<-trans; <-≤-trans; ≃-<ʳ; ≃-sym; lt-add; 0<1; nat-suc; nat-bound) renaming (nat to natℚ)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Continuous.Monus using (module Monus)

open Cut using (mem; down)
open _⊑_ using (ap)

module MonusAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; refl; sym; trans; +-cong; +-identityʳ; ≤-trans; ≤-reflexive; 0-least;
    ≤-+ʳ; +-comm)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open Near (lemOf lem₁) using (cancel-bnd-⊑)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat)
  open LebesgueShiftAlg (lemOf lem₁) using (bnd-rat)
  open Monus lem₁ using (monus; monus-add; monus-zero)

  BndQ-≤ : ∀ {a b : Cut} → a ≤ b → BndQ b → BndQ a
  BndQ-≤ le (M , bd) = M , λ r m → bd r (ap le r m)

  BndQ-≈ : ∀ {a b : Cut} → a ≈ b → BndQ b → BndQ a
  BndQ-≈ e = BndQ-≤ (proj₁ e)

  BndQ-add : ∀ {a b : Cut} → BndQ a → BndQ b → BndQ (a + b)
  BndQ-add (M , bd) (M′ , bd′) = M +ℚ M′ , λ q (r , s , mr , ms , le) →
    ≤-<-trans le (ℚP.+-mono-< (bd r mr) (bd′ s ms))

  BndQ-0 : BndQ 0#
  BndQ-0 = natℚ 0 , λ r lt → lt

  -- a rational bound gives a natural-number bound
  rat-bnd : ∀ t → BndQ t → Bnd t
  rat-bnd t (M , bd) = suc k , ≤-trans (mk⊑ (λ r mr → ap (proj₂ (natE≋ (lemOf lem₁) k)) r (lt r mr)))
    (≤-reflexive (natE≈nat (suc k)))
    where
      k = proj₁ (nat-bound M)
      lt : ∀ r → mem t r → r <ℚ natℚ (suc k)
      lt r mr = <-trans (<-≤-trans (bd r mr) (proj₂ (nat-bound M))) (≃-<ʳ (≃-sym (nat-suc k)) (lt-add 0<1))

  -- any two lower reals are comparable
  cut-total : ∀ (a b : Cut) → a ≤ b ⊎ b ≤ a
  cut-total a b with lemOf lem₁ (Σ ℚᵘ (λ q → mem b q × (mem a q → ⊥)))
  ... | inj₁ (q , mb , na) = inj₁ (mk⊑ (λ r ma → down b (below r ma (≤-or-> r q)) mb))
    where
      below : ∀ r → mem a r → _ → _
      below r ma (inj₁ le) = le
      below r ma (inj₂ lt) = ⊥-elim (na (down a (<-≤ lt) ma))
  ... | inj₂ none = inj₂ (mk⊑ (λ r mb → inc r mb (lemOf lem₁ (mem a r))))
    where
      inc : ∀ r → mem b r → _ → _
      inc r mb (inj₁ ma) = ma
      inc r mb (inj₂ na) = ⊥-elim (none (r , mb , na))

  -- x ∸ t ≤ x
  monus-le : ∀ x t → Bnd t → monus x t ≤ x
  monus-le x t bt with cut-total t x
  ... | inj₁ tx = ≤-trans ≤-+ʳ′ (≤-reflexive (monus-add x t bt tx))
    where ≤-+ʳ′ = ≤-trans (≤-+ʳ {monus x t} {t}) (≤-reflexive (+-comm (monus x t) t))
  ... | inj₂ xt = ≤-trans (≤-reflexive (monus-zero x t xt)) 0-least

  -- d ≤ e + ε gives d ∸ e ≤ ε, for e bounded
  monus-small : ∀ d e k → Bnd e → d ≤ e + hp k → monus d e ≤ hp k
  monus-small d e k be h with cut-total e d
  ... | inj₁ ed = cancel-bnd-⊑ {e} {monus d e} {hp k} (bnd-rat e be) (≤-trans (≤-reflexive (monus-add d e be ed)) h)
  ... | inj₂ de = ≤-trans (≤-reflexive (monus-zero d e de)) 0-least

  -- d + (e ∸ d) ≈ e + (d ∸ e)
  monus-swap : ∀ d e → Bnd d → Bnd e → d + monus e d ≈ e + monus d e
  monus-swap d e bd be with cut-total d e
  ... | inj₁ de = trans (monus-add e d bd de) (sym (trans (+-cong refl (monus-zero d e de)) (+-identityʳ e)))
  ... | inj₂ ed = trans (trans (+-cong refl (monus-zero e d ed)) (+-identityʳ d)) (sym (monus-add d e be ed))
