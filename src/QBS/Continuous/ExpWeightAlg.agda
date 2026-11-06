{-# OPTIONS --safe --without-K #-}

-- Multiplicative cancellation and rearrangement identities for exponential weights (plan 07, item 58; helper for
-- `Continuous/ExpWeight`), over an abstract commutative monoid.
--   * `cancel-mul`: cancellation of units;
--   * `cancel-3`: 3-fold unit product cancellation;
--   * `rearrange-step`, `rearrange-step′`: rearrangement of weight factors against cancelled components.
-- Route: `Algebra.Solver.CommutativeMonoid`.
module QBS.Continuous.ExpWeightAlg where

open import Algebra.Bundles using (CommutativeMonoid)
import Algebra.Solver.CommutativeMonoid as CMSolver

module ExpWeightRing {c ℓ} (M : CommutativeMonoid c ℓ) where
  open CommutativeMonoid M using (Carrier; _≈_; refl; sym; trans)
    renaming (_∙_ to _*_; ε to 1#; ∙-cong to *-cong; identityˡ to *-identityˡ; identityʳ to *-identityʳ
             ; assoc to *-assoc; comm to *-comm)
  open CMSolver M renaming (_⊕_ to _⊙_; _⊜_ to _≐_)

  cancel-mul : ∀ x y c d → c * d ≈ 1# → x * c ≈ y * c → x ≈ y
  cancel-mul x y c d cd eq =
    trans (sym (*-identityʳ x))
      (trans (*-cong refl (sym cd))
        (trans (sym (*-assoc x c d))
          (trans (*-cong eq refl)
            (trans (*-assoc y c d)
              (trans (*-cong refl cd) (*-identityʳ y))))))

  cancel-3 : ∀ {a₁ a₂ b₁ b₂ c₁ c₂} →
    a₁ * a₂ ≈ 1# → b₁ * b₂ ≈ 1# → c₁ * c₂ ≈ 1# →
    ((a₁ * b₁) * c₁) * ((a₂ * b₂) * c₂) ≈ 1#
  cancel-3 {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} ha hb hc =
    trans (solve 6 (λ a₁ a₂ b₁ b₂ c₁ c₂ →
      ((a₁ ⊙ b₁) ⊙ c₁) ⊙ ((a₂ ⊙ b₂) ⊙ c₂) ≐ ((a₁ ⊙ a₂) ⊙ (b₁ ⊙ b₂)) ⊙ (c₁ ⊙ c₂))
      refl a₁ a₂ b₁ b₂ c₁ c₂)
      (trans (*-cong (*-cong ha hb) hc)
        (trans (*-cong (*-identityˡ 1#) refl) (*-identityˡ 1#)))

  rearrange-step : ∀ ps ns n_s n_t k →
    ns * n_s ≈ 1# →
    (ps * ns) * ((n_s * n_t) * k) ≈ (ps * n_t) * k
  rearrange-step ps ns n_s n_t k h =
    trans (solve 5 (λ ps ns n_s n_t k →
      (ps ⊙ ns) ⊙ ((n_s ⊙ n_t) ⊙ k) ≐ (ns ⊙ n_s) ⊙ ((ps ⊙ n_t) ⊙ k))
      refl ps ns n_s n_t k)
      (trans (*-cong h refl) (*-identityˡ _))

  rearrange-step′ : ∀ pt nt n_s n_t k →
    nt * n_t ≈ 1# →
    (pt * nt) * ((n_s * n_t) * k) ≈ (pt * n_s) * k
  rearrange-step′ pt nt n_s n_t k h =
    trans (solve 5 (λ pt nt n_s n_t k →
      (pt ⊙ nt) ⊙ ((n_s ⊙ n_t) ⊙ k) ≐ (nt ⊙ n_t) ⊙ ((pt ⊙ n_s) ⊙ k))
      refl pt nt n_s n_t k)
      (trans (*-cong h refl) (*-identityˡ _))

  ud-step : ∀ ep en p e n →
    n * e ≈ 1# →
    (p * n) * en ≈ ep →
    ep * e ≈ p * en
  ud-step ep en p e n hne hud =
    trans (*-cong (sym hud) refl)
      (trans (solve 4 (λ p n en e → ((p ⊙ n) ⊙ en) ⊙ e ≐ (n ⊙ e) ⊙ (p ⊙ en)) refl p n en e)
        (trans (*-cong hne refl) (*-identityˡ _)))
