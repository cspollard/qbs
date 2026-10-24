{-# OPTIONS --safe --without-K #-}

-- Order facts about ½ and the affine maps s ↦ ½s and s ↦ ½ + ½s, in any semiring with a half
-- (`Arch`): the inequalities behind the self-similarity of the binary expansion.
module QBS.Analysis.HalfOrder where

open import Level using (suc; zero)
open import Data.Product.Base using (_×_; _,_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Archimedean using (Arch)

module HalfOrder (A : OmegaSemiring (suc zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; cancel≤) renaming (half+half to hh)
  open SetoidReasoning setoid

  half≤1 : half ≤ 1#
  half≤1 = ≤-trans ≤-+ʳ (≤-reflexive hh)

  half-twice : ∀ x → half * (x + x) ≈ x
  half-twice x = begin
    half * (x + x)       ≈⟨ distribˡ half x x ⟩
    half * x + half * x  ≈⟨ sym (distribʳ x half half) ⟩
    (half + half) * x    ≈⟨ *-cong hh refl ⟩
    1# * x               ≈⟨ *-identityˡ x ⟩
    x ∎

  -- halving reflects the order
  half-cancel : ∀ {x y} → half * x ≤ half * y → x ≤ y
  half-cancel {x} {y} h = ≤-resp (half-twice x) (half-twice y)
    (≤-trans (≤-reflexive (distribˡ half x x)) (≤-trans (+-mono h h) (≤-reflexive (sym (distribˡ half y y)))))

  -- first bit false: x′ = ½x
  false-iff : ∀ {x x′ y} → x′ ≈ half * x → (x′ ≤ half * y → x ≤ y) × (x ≤ y → x′ ≤ half * y)
  false-iff e = (λ h → half-cancel (≤-resp e refl h)) , (λ h → ≤-trans (≤-reflexive e) (*-mono half h))

  -- first bit true: x′ = ½ + ½x
  true-iff : ∀ {x x′ y} → x′ ≈ half + half * x → (x′ ≤ half + half * y → x ≤ y) × (x ≤ y → x′ ≤ half + half * y)
  true-iff e = (λ h → half-cancel (cancel≤ half≤1 (≤-resp e refl h)))
             , (λ h → ≤-trans (≤-reflexive e) (+-mono ≤-refl (*-mono half h)))

  -- … lands below ½s only for s ≤ 1 when x = 0
  true-null : ∀ {x x′ s} → x′ ≈ half + half * x → s ≤ 1# → x′ ≤ half * s → x ≤ 0#
  true-null {x} {x′} {s} e s≤1 h = half-cancel (≤-trans (cancel≤ half≤1 step) (≤-reflexive (sym (zeroʳ half))))
    where
      step : half + half * x ≤ half + 0#
      step = ≤-trans (≤-reflexive (sym e))
        (≤-trans h (≤-trans (*-mono half s≤1)
          (≤-reflexive (trans (*-identityʳ half) (sym (+-identityʳ half))))))

  -- … never lands below 0
  true-pos : ∀ {x x′} → x′ ≈ half + half * x → x′ ≤ half * 0# → half ≤ 0#
  true-pos e h = ≤-trans ≤-+ʳ (≤-trans (≤-reflexive (sym e)) (≤-trans h (≤-reflexive (zeroʳ half))))

  -- first bit false always lands below ½ + ½s
  false-top : ∀ {x x′ s} → x′ ≈ half * x → x ≤ 1# → x′ ≤ half + half * s
  false-top {x} {x′} {s} e x≤1 =
    ≤-trans (≤-reflexive e) (≤-trans (*-mono half x≤1)
      (≤-trans (≤-reflexive (*-identityʳ half)) ≤-+ʳ))

  -- rewriting the two summands of ½a + ½b
  mix2 : ∀ {x a b a′ b′} → x ≈ half * a + half * b → a ≈ a′ → b ≈ b′ → x ≈ half * a′ + half * b′
  mix2 e ea eb = trans e (+-cong (*-cong refl ea) (*-cong refl eb))
