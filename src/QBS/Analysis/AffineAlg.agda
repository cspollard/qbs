{-# OPTIONS --safe --without-K #-}

-- Algebra for moments of pushforward (affine) families, generic over an `OmegaSemiring` (so the ring solver never sees concrete cuts).
--   * `var-core`: if `E₁ ≃ a`, `E₂ ≃ d` are finite signed values with `d ≈ s + a·a`, then `E₂ − E₁² ≃ s`
--     (the variance of a family whose second moment is `s + a²`: for Exp(c), `a = c`, `d = 2c²`, `s = c²`);
--   * `mean-aff`: if `X₁ ≃ 0` and `E₁ ≃ m + s·X₁` then `E₁ ≃ m`;
--   * `var-aff`: if `X₁ ≃ 0`, `X₂ ≃ 1`, `E₁ ≃ m + s·X₁` and `E₂ ≃ (m² + (m+m)s·X₁) + s²·X₂` (the moments of `Y = m + sX` from
--     those of the standard variable `X`: `E[Y²] = m² + 2ms E[X] + s² E[X²]`) then `E₂ − E₁² ≃ s²`, for signed `m`, `s`;
--   * `scale-ι`: `a·b ≈ s` gives `ι a · ι b ≃ ι s`;
--   * `moment-two`: `c²·2 ≈ c² + (c·1)(c·1)` for the first two moments `c¹·1!`, `c²·2!` of an exponential scale family.
module QBS.Analysis.AffineAlg where

import Level as L
open import Data.Product.Base using (_,_)

open import QBS.Analysis.Omega
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)

module AlgAff (A : OmegaSemiring (L.suc L.zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Bounded A using (Sg; Bnd; finite; _≃_; mk≃; ≃-refl; ≃-trans; _+S_; _*S_; -S_; ι; +S-cong;
      -S-cong; *S-cong; *S-congʳ; 0S; 1S; _−_[_,_])
  open SubSemiring using (Is-0; Is-+; Is-*)
  open Sg
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
    using (solve; _:+_; _:*_; _:=_; con)

  -- `ι` respects `≈`
  ι-cong : ∀ {a b} (fa : Bnd a) (fb : Bnd b) → a ≈ b → ι fa ≃ ι fb
  ι-cong fa fb e = mk≃ 0# (Is-0 finite) (+-cong (+-cong e refl) refl)

  -- the variance of a family with `E₂ = s + E₁²`
  core : ∀ {a s} (ba : Bnd a) (bs : Bnd s) →
    (ι (Is-+ finite bs (Is-* finite ba ba)) +S (-S (ι ba *S ι ba))) ≃ ι bs
  core {a} {s} ba bs = mk≃ 0# (Is-0 finite) (solve 2 (λ a s →
    ((((s :+ (a :* a)) :+ ((a :* con 0) :+ (con 0 :* a))) :+ con 0) :+ con 0) := ((s :+ (con 0 :+
        ((a :* a) :+ (con 0 :* con 0)))) :+ con 0))
    refl a s)

  var-core : ∀ {a d s} (ba : Bnd a) (bd : Bnd d) (bs : Bnd s) → d ≈ s + a * a → (E₁ E₂ : Sg) → E₁ ≃ ι ba → E₂ ≃ ι bd →
    (E₂ +S (-S (E₁ *S E₁))) ≃ ι bs
  var-core ba bd bs hd E₁ E₂ e₁ e₂ = ≃-trans (+S-cong e₂ (-S-cong (*S-cong e₁ e₁)))
    (≃-trans (+S-cong (ι-cong bd (Is-+ finite bs (Is-* finite ba ba)) hd) ≃-refl) (core ba bs))

  -- the exponential scale family: `c²·f₂ ≈ c² + (c·f₁)(c·f₁)` when `f₁ ≈ 1`, `f₂ ≈ 1 + 1`
  moment-two : ∀ c f₁ f₂ → f₁ ≈ 1# → f₂ ≈ 1# + 1# → (c * (c * 1#)) * f₂ ≈ (c * (c * 1#)) + ((c * 1#)
      * f₁) * ((c * 1#) * f₁)
  moment-two c f₁ f₂ h₁ h₂ = trans (*-cong refl h₂)
    (trans (solve 1 (λ c → (c :* (c :* con 1)) :* (con 1 :+ con 1) := (c :* (c :* con 1)) :+ ((c :*
        con 1) :* con 1) :* ((c :* con 1) :* con 1)) refl c)
      (+-cong refl (*-cong (*-cong refl (sym h₁)) (*-cong refl (sym h₁)))))

  -- the product of two finite elements as signed values
  scale-ι : ∀ {a b s} (ba : Bnd a) (bb : Bnd b) (bs : Bnd s) → a * b ≈ s → (ι ba *S ι bb) ≃ ι bs
  scale-ι {a} {b} ba bb bs h = mk≃ 0# (Is-0 finite) (trans
    (solve 2 (λ a b → (((a :* b :+ con 0 :* con 0) :+ con 0) :+ con 0) := ((a :* b :+ ((a :* con 0)
        :+ (con 0 :* b))) :+ con 0)) refl a b)
    (+-cong (+-cong h refl) refl))

  -- three small laws of the signed ring (each a single solve)
  kill0 : ∀ x t → (x +S (t *S 0S)) ≃ x
  kill0 x t = mk≃ 0# (Is-0 finite) (solve 4 (λ a b c d →
    a :+ (c :* con 0 :+ d :* con 0) :+ b :+ con 0 := a :+ (b :+ (c :* con 0 :+ d :* con 0)) :+ con 0)
    refl (pos x) (neg x) (pos t) (neg t))

  kill01 : ∀ x t y → ((x +S (t *S 0S)) +S (y *S 1S)) ≃ (x +S y)
  kill01 x t y = mk≃ 0# (Is-0 finite) (solve 6 (λ a b c d e f →
    a :+ (c :* con 0 :+ d :* con 0) :+ (e :* con 1 :+ f :* con 0) :+ (b :+ f) :+ con 0
      := a :+ e :+ (b :+ (c :* con 0 :+ d :* con 0) :+ (e :* con 0 :+ f :* con 1)) :+ con 0)
    refl (pos x) (neg x) (pos t) (neg t) (pos y) (neg y))

  cancelS : ∀ x y → ((x +S y) +S (-S x)) ≃ y
  cancelS x y = mk≃ 0# (Is-0 finite) (solve 4 (λ a b e f → a :+ e :+ b :+ f :+ con 0 := e :+ (b :+ f :+ a) :+ con 0)
    refl (pos x) (neg x) (pos y) (neg y))

  -- an affine statistic `m + sX` of a standard variable with `E X ≃ 0`
  mean-aff : ∀ (m s X₁ E₁ : Sg) → X₁ ≃ 0S → E₁ ≃ (m +S (s *S X₁)) → E₁ ≃ m
  mean-aff m s X₁ E₁ h e = ≃-trans e (≃-trans (+S-cong ≃-refl (*S-congʳ s h)) (kill0 m s))

  -- `Var(m + sX) = s²` when `E X = 0`, `E X² = 1`
  var-aff : ∀ (m s X₁ X₂ E₁ E₂ : Sg) → X₁ ≃ 0S → X₂ ≃ 1S → E₁ ≃ (m +S (s *S X₁)) →
    E₂ ≃ (((m *S m) +S (((m +S m) *S s) *S X₁)) +S ((s *S s) *S X₂)) → (E₂ +S (-S (E₁ *S E₁))) ≃ (s *S s)
  var-aff m s X₁ X₂ E₁ E₂ h₁ h₂ e₁ e₂ = ≃-trans (+S-cong e₂ (-S-cong (*S-cong m₁ m₁)))
    (≃-trans (+S-cong (+S-cong (+S-cong ≃-refl (*S-congʳ ((m +S m) *S s) h₁)) (*S-congʳ (s *S s) h₂)) ≃-refl)
      (≃-trans (+S-cong (kill01 (m *S m) ((m +S m) *S s) (s *S s)) ≃-refl) (cancelS (m *S m) (s *S s))))
    where m₁ : E₁ ≃ m
          m₁ = mean-aff m s X₁ E₁ h₁ e₁
