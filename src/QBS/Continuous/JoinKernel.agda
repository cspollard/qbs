{-# OPTIONS --safe --without-K #-}

-- Shared kernel construction for the join of the probability and s-finite monads: given a witness that a random family of
-- measures on X has outer kernel `g` and, at each merged parameter, inner kernel `G`, the join is realised by the
-- kernel `g′ r = bind (g r) (s ↦ push (merge₁ …) (G (merge r s)))`.  Nothing here mentions weights or the measure
-- class, so `Continuous.Monad.JoinWit` and `Continuous.SFiniteMonad.JoinWit` both use it and add only the probes.
module QBS.Continuous.JoinKernel where

import Level as L
open import Level using (lower)
open import Function.Bundles using (_⟨$⟩_)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (down)
open import QBS.Borel.Merge using (mergeC; measurable-merge; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Param
open import QBS.Continuous.Sample
open import QBS.Classical using (LEM₀)

module JoinKernel (A : OmegaSemiring (L.suc L.zero)) (lem : LEM₀) where
  open Integration A
  open Measurable A
  module P₁ = Param A lem mergeC measurable-merge₁ Cyl-rect

  -- the inner measure on u = merge s t, given the merged parameter k = merge r s
  module Inner (G : R → Measure) (Gok : KernelOk G) where
    K′ : R → Measure
    K′ k = push {mergeR (oddsR k)} (measurable-merge₁ (lower (oddsR k))) (G k)

    kK′ : KernelOk K′
    kK′ {h} fh = Fun-ext
      (λ k → I-cong (G k)
               (λ t → Fun-resp lem fh (lower (mergeR-cong (oddsR-cong (merge-evens k t)) (merge-odds k t)))) _ _)
      (P₁.PF G Gok {λ x → h (φ x)} (Fun-pre {h} {φ} fh mφ))
      where
        φ : R → R
        φ x = mergeR (oddsR (evensR x)) (oddsR x)
        mφ : Measurable (down φ)
        mφ = measurable-merge (measurable-∘ measurable-evens measurable-odds) measurable-odds

    -- the joined outer measure at r, for an outer kernel g
    module Outer (g : R → Measure) (gok : KernelOk g) where
      gK : R → R → Measure
      gK r s = K′ (mergeR r s)

      kgK : ∀ r → KernelOk (gK r)
      kgK r fh = Fun-pre (kK′ fh) (measurable-merge₁ (lower r))

      g′ : R → Measure
      g′ r = bind (g r) (gK r) (kgK r)

      gok′ : KernelOk g′
      gok′ fh = P₁.PF g gok (kK′ fh)
