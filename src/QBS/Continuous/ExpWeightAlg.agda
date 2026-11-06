{-# OPTIONS --safe --without-K #-}

-- Multiplicative cancellation and rearrangement identities for exponential weights (plan 07, item 58; helper for
-- `Continuous/ExpWeight`), over an abstract commutative monoid.
--   * `cancel-mul`: cancellation of units;
--   * `cancel-3`: 3-fold unit product cancellation;
--   * `rearrange-step`, `rearrange-step′`: rearrangement of weight factors against cancelled components;
--   * `ud-step`: from n e ≈ 1 and (p n) eₙ ≈ eₚ, eₚ e ≈ p eₙ (the step of `ExpWeight.log-expW`).
-- Route: `Algebra.Solver.CommutativeMonoid` for the rearrangements, in setoid reasoning chains.
module QBS.Continuous.ExpWeightAlg where

open import Algebra.Bundles using (CommutativeMonoid)
import Algebra.Solver.CommutativeMonoid as CMSolver
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module ExpWeightAlg {c ℓ} (M : CommutativeMonoid c ℓ) where
  open CommutativeMonoid M using (Carrier; _≈_; refl; sym; setoid)
    renaming (_∙_ to _*_; ε to 1#; ∙-cong to *-cong; identityˡ to *-identityˡ; identityʳ to *-identityʳ
             ; assoc to *-assoc)
  open CMSolver M renaming (_⊕_ to _⊙_; _⊜_ to _≐_)
  open SetoidReasoning setoid

  cancel-mul : ∀ x y c d → c * d ≈ 1# → x * c ≈ y * c → x ≈ y
  cancel-mul x y c d cd eq = begin
    x            ≈⟨ sym (*-identityʳ x) ⟩
    x * 1#       ≈⟨ *-cong refl (sym cd) ⟩
    x * (c * d)  ≈⟨ sym (*-assoc x c d) ⟩
    (x * c) * d  ≈⟨ *-cong eq refl ⟩
    (y * c) * d  ≈⟨ *-assoc y c d ⟩
    y * (c * d)  ≈⟨ *-cong refl cd ⟩
    y * 1#       ≈⟨ *-identityʳ y ⟩
    y            ∎

  cancel-3 : ∀ {a₁ a₂ b₁ b₂ c₁ c₂} →
    a₁ * a₂ ≈ 1# → b₁ * b₂ ≈ 1# → c₁ * c₂ ≈ 1# →
    ((a₁ * b₁) * c₁) * ((a₂ * b₂) * c₂) ≈ 1#
  cancel-3 {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} ha hb hc = begin
    ((a₁ * b₁) * c₁) * ((a₂ * b₂) * c₂)
      ≈⟨ solve 6 (λ a₁ a₂ b₁ b₂ c₁ c₂ →
           ((a₁ ⊙ b₁) ⊙ c₁) ⊙ ((a₂ ⊙ b₂) ⊙ c₂) ≐ ((a₁ ⊙ a₂) ⊙ (b₁ ⊙ b₂)) ⊙ (c₁ ⊙ c₂))
           refl a₁ a₂ b₁ b₂ c₁ c₂ ⟩
    ((a₁ * a₂) * (b₁ * b₂)) * (c₁ * c₂)  ≈⟨ *-cong (*-cong ha hb) hc ⟩
    (1# * 1#) * 1#                       ≈⟨ *-cong (*-identityˡ 1#) refl ⟩
    1# * 1#                              ≈⟨ *-identityˡ 1# ⟩
    1#                                   ∎

  rearrange-step : ∀ ps ns n_s n_t k →
    ns * n_s ≈ 1# →
    (ps * ns) * ((n_s * n_t) * k) ≈ (ps * n_t) * k
  rearrange-step ps ns n_s n_t k h = begin
    (ps * ns) * ((n_s * n_t) * k)
      ≈⟨ solve 5 (λ ps ns n_s n_t k → (ps ⊙ ns) ⊙ ((n_s ⊙ n_t) ⊙ k) ≐ (ns ⊙ n_s) ⊙ ((ps ⊙ n_t) ⊙ k))
           refl ps ns n_s n_t k ⟩
    (ns * n_s) * ((ps * n_t) * k)  ≈⟨ *-cong h refl ⟩
    1# * ((ps * n_t) * k)          ≈⟨ *-identityˡ _ ⟩
    (ps * n_t) * k                 ∎

  rearrange-step′ : ∀ pt nt n_s n_t k →
    nt * n_t ≈ 1# →
    (pt * nt) * ((n_s * n_t) * k) ≈ (pt * n_s) * k
  rearrange-step′ pt nt n_s n_t k h = begin
    (pt * nt) * ((n_s * n_t) * k)
      ≈⟨ solve 5 (λ pt nt n_s n_t k → (pt ⊙ nt) ⊙ ((n_s ⊙ n_t) ⊙ k) ≐ (nt ⊙ n_t) ⊙ ((pt ⊙ n_s) ⊙ k))
           refl pt nt n_s n_t k ⟩
    (nt * n_t) * ((pt * n_s) * k)  ≈⟨ *-cong h refl ⟩
    1# * ((pt * n_s) * k)          ≈⟨ *-identityˡ _ ⟩
    (pt * n_s) * k                 ∎

  ud-step : ∀ ep en p e n →
    n * e ≈ 1# →
    (p * n) * en ≈ ep →
    ep * e ≈ p * en
  ud-step ep en p e n hne hud = begin
    ep * e              ≈⟨ *-cong (sym hud) refl ⟩
    ((p * n) * en) * e  ≈⟨ solve 4 (λ p n en e → ((p ⊙ n) ⊙ en) ⊙ e ≐ (n ⊙ e) ⊙ (p ⊙ en)) refl p n en e ⟩
    (n * e) * (p * en)  ≈⟨ *-cong hne refl ⟩
    1# * (p * en)       ≈⟨ *-identityˡ _ ⟩
    p * en              ∎
