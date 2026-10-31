{-# OPTIONS --safe --without-K #-}

-- Interleaving of clopen trees: `interleave t₁ t₂` is the clopen set {merge a s | a ∈ t₁, s ∈ t₂}
-- (even coordinates read by t₁, odd ones by t₂), with its dyadic measure the product
-- `μ0 t₁ * μ0 t₂`.  This gives the independence of the even and odd bits of the fair coin.
module QBS.Analysis.Interleave where

import Level as L
open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
import Data.Bool.Properties as B
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Data.Product.Base using (_×_; _,_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core using (Cantor)
open import QBS.Borel.Merge using (mergeC; mergeBit; ev; hf)
open import QBS.Analysis.Omega
open import QBS.Analysis.Clopen
open import QBS.Analysis.Archimedean
open import QBS.Analysis.ClopenMeasure

-- the tree reading only the odd coordinates: {merge a s | s ∈ t}
stutter : Cl → Cl
stutter (leaf b) = leaf b
stutter (split l r) = split (split (stutter l) (stutter r)) (split (stutter l) (stutter r))

interleave : Cl → Cl → Cl
interleave (split l r) t = split (interleave t l) (interleave t r)
interleave (leaf false) t = leaf false
interleave (leaf true) t = stutter t

----------------------------------------------------------------------------
-- semantics

private
  -- ev (suc n) and hf (suc n) in terms of ev n and hf n
  ev-suc : ∀ n → ev (suc n) ≡ not (ev n)
  ev-suc zero = refl
  ev-suc (suc zero) = refl
  ev-suc (suc (suc n)) = ev-suc n

  hf-suc : ∀ n → hf (suc n) ≡ (if ev n then hf n else suc (hf n))
  hf-suc zero = refl
  hf-suc (suc zero) = refl
  hf-suc (suc (suc n)) = trans (cong suc (hf-suc n)) (lem (ev n) (hf n))
    where lem : ∀ (b : Bool) k → suc (if b then k else suc k) ≡ (if b then suc k else suc (suc k))
          lem true k = refl
          lem false k = refl

  suc-bits : ∀ n b → ev n ≡ b → (ev (suc n) , hf (suc n)) ≡ (not b , (if b then hf n else suc (hf n)))
  suc-bits n b e = ≡.cong₂ _,_ (trans (ev-suc n) (cong not e))
                              (trans (hf-suc n) (cong (λ c → if c then hf n else suc (hf n)) e))

  tl-merge : ∀ a s n → tl (mergeC a s) n ≡ mergeC s (tl a) n
  tl-merge a s n = go n (ev n) refl
    where
      bit : Bool × ℕ → Bool
      bit (c , k) = mergeBit c (a k) (s k)

      go : ∀ n b → ev n ≡ b → tl (mergeC a s) n ≡ mergeC s (tl a) n
      go n true e = trans (cong bit (suc-bits n true e)) (sym (cong (λ c → mergeBit c (s (hf n)) (a (suc (hf n)))) e))
      go n false e = trans (cong bit (suc-bits n false e)) (sym (cong (λ c → mergeBit c (s (hf n)) (a (suc (hf n)))) e))

  tl2-merge : ∀ a s n → tl (tl (mergeC a s)) n ≡ mergeC (tl a) (tl s) n
  tl2-merge a s n = trans (tl-merge a s (suc n)) (tl-merge s (tl a) n)

  pick : ∀ (b : Bool) {u v u′ v′ g : Bool} → u ≡ u′ ∧ g → v ≡ v′ ∧ g →
    (if b then v else u) ≡ (if b then v′ else u′) ∧ g
  pick false hu hv = hu
  pick true hu hv = hv

  pick′ : ∀ (b : Bool) {u v u′ v′ g : Bool} → u ≡ g ∧ u′ → v ≡ g ∧ v′ →
    (if b then v else u) ≡ g ∧ (if b then v′ else u′)
  pick′ false hu hv = hu
  pick′ true hu hv = hv

eval-stutter : ∀ t a s → eval (stutter t) (mergeC a s) ≡ eval t s
eval-stutter (leaf b) a s = refl
eval-stutter (split l r) a s =
  trans (B.if-eta (a 0))
    (B.if-cong₂ (s 0)
      (trans (eval-ext (stutter r) (tl2-merge a s)) (eval-stutter r (tl a) (tl s)))
      (trans (eval-ext (stutter l) (tl2-merge a s)) (eval-stutter l (tl a) (tl s))))

eval-interleave : ∀ t₁ t₂ a s →
  eval (interleave t₁ t₂) (mergeC a s) ≡ eval t₁ a ∧ eval t₂ s
eval-interleave (split l r) t₂ a s =
  pick (a 0)
    (trans (eval-ext (interleave t₂ l) (tl-merge a s))
      (trans (eval-interleave t₂ l s (tl a)) (B.∧-comm (eval t₂ s) (eval l (tl a)))))
    (trans (eval-ext (interleave t₂ r) (tl-merge a s))
      (trans (eval-interleave t₂ r s (tl a)) (B.∧-comm (eval t₂ s) (eval r (tl a)))))
eval-interleave (leaf false) t₂ a s = refl
eval-interleave (leaf true) t₂ a s = eval-stutter t₂ a s

----------------------------------------------------------------------------
-- the dyadic measure of an interleaving is the product

module Product {A : OmegaSemiring (L.suc L.zero)} (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; refl to rfl; sym to sm; trans to tr)
  open Arch R using (half; half-twice)
  open Premeasure R using (μ0)
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  μ0-stutter : ∀ t → μ0 (stutter t) ≈ μ0 t
  μ0-stutter (leaf b) = rfl
  μ0-stutter (split l r) = begin
    half * (y + y)   ≈⟨ half-twice y ⟩
    y                ≈⟨ *-cong rfl (+-cong (μ0-stutter l) (μ0-stutter r)) ⟩
    half * (μ0 l + μ0 r) ∎
    where y = half * (μ0 (stutter l) + μ0 (stutter r))

  μ0-interleave : ∀ t₁ t₂ → μ0 (interleave t₁ t₂) ≈ μ0 t₁ * μ0 t₂
  μ0-interleave (leaf false) t₂ = sm (zeroˡ (μ0 t₂))
  μ0-interleave (leaf true) t₂ = tr (μ0-stutter t₂) (sm (*-identityˡ (μ0 t₂)))
  μ0-interleave (split l r) t₂ = begin
    half * (μ0 (interleave t₂ l) + μ0 (interleave t₂ r))
      ≈⟨ *-cong rfl (+-cong (μ0-interleave t₂ l) (μ0-interleave t₂ r)) ⟩
    half * (μ0 t₂ * μ0 l + μ0 t₂ * μ0 r)
      ≈⟨ solve 4 (λ h t a b → h :* (t :* a :+ t :* b) := (h :* (a :+ b)) :* t) rfl half (μ0 t₂) (μ0 l) (μ0 r) ⟩
    (half * (μ0 l + μ0 r)) * μ0 t₂ ∎
