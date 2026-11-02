{-# OPTIONS --safe --without-K #-}

-- The signed arithmetic of the moments of the exponential with a rate λ, over an abstract Archimedean ω-semiring (the
-- concrete cut semiring makes Agda unify the huge signed expressions too slowly):
--   * `var-val`: with `V₁ = (c·1! − 0)` and `V₂ = (c²·2! − 0)` as signed values, `(V₂ − V₁·V₁) · ι(λ²) ≃ 1`, for
--     `f₁ ≈ 1`, `f₂ ≈ 1 + 1` and `λ c ≈ 1` (the variance of Exp(λ), rescaled by λ²);
--   * `var-gen`: the same for any signed `E₁ ≃ V₁`, `E₂ ≃ V₂` (the expectations), by the congruences of `Sg`.
module QBS.Analysis.ExpRateSigned where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.ExpRate using (module AlgRate)

module AlgSigned (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) (l c : OmegaSemiring.Carrier A)
  (lc : OmegaSemiring._≈_ A (OmegaSemiring._*_ A l c) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; finite; Sg; _≃_; mk≃; ≃-trans; _−_[_,_]; _+S_; _*S_; -S_; ι; +S-cong; -S-cong; *S-cong; *S-congˡ)
  open SubSemiring using (Is-0; Is-1)
  open AlgP A R using (pw)
  open AlgRate A R using (module Sc)
  open Sc l c lc using (var-eq)

  var-val : ∀ f1 f2 (b1 : Bnd (pw 1 c * f1)) (b2 : Bnd (pw 2 c * f2)) (bl : Bnd (pw 2 l)) → f1 ≈ 1# → f2 ≈ 1# + 1# →
    (((((pw 2 c * f2) − 0# [ b2 , Is-0 finite ]) +S
        (-S (((pw 1 c * f1) − 0# [ b1 , Is-0 finite ]) *S ((pw 1 c * f1) − 0# [ b1 , Is-0 finite ])))) *S ι bl))
    ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  var-val f1 f2 b1 b2 bl h1 h2 = mk≃ 0# (Is-0 finite) (var-eq f1 f2 h1 h2)

  -- the variance of any signed `E₁ ≃ c·f₁ − 0`, `E₂ ≃ c²·f₂ − 0`, rescaled by λ²
  var-gen : ∀ f1 f2 (b1 : Bnd (pw 1 c * f1)) (b2 : Bnd (pw 2 c * f2)) (bl : Bnd (pw 2 l)) (E1 E2 : Sg) →
    E1 ≃ ((pw 1 c * f1) − 0# [ b1 , Is-0 finite ]) → E2 ≃ ((pw 2 c * f2) − 0# [ b2 , Is-0 finite ]) →
    f1 ≈ 1# → f2 ≈ 1# + 1# → ((E2 +S (-S (E1 *S E1))) *S ι bl) ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  var-gen f1 f2 b1 b2 bl E1 E2 e1 e2 h1 h2 = ≃-trans
    (*S-congˡ (ι bl) (+S-cong e2 (-S-cong (*S-cong e1 e1)))) (var-val f1 f2 b1 b2 bl h1 h2)
