{-# OPTIONS --safe --without-K #-}

-- A self-similar distribution function is the identity.  Let F, Z : [0,∞] → [0,∞] be monotone
-- with F(0) = 0 forced by
--   F(½s)     = ½ Z(s) + ½ F(s)      (Z(s) ≤ F(0), Z(0) = 0)
--   F(½ + ½s) = ½ F(s) + ½
-- for s ≤ 1, and F(1) = 1.  (For the uniform distribution F(t) = μ{expansion ≤ t}, the two laws
-- come from splitting off the first bit.)  Then F t = t for all t ≤ 1: the set G = {x | F x = x}
-- contains 0 and 1 and is closed under s ↦ ½s and s ↦ ½ + ½s, so every t ≤ 1 is squeezed
-- between two elements of G that are 2⁻ⁿ apart; an Archimedean argument finishes.
module QBS.Analysis.SelfSimilar where

open import Level using (suc; zero)
open import Function.Base using (case_of_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)

module SelfSimilar (A : OmegaSemiring (suc zero)) (R : Arch A)
    (tot : ∀ t → OmegaSemiring._≤_ A t (Arch.half R) ⊎ OmegaSemiring._≤_ A (Arch.half R) t)
    (F Z : OmegaSemiring.Carrier A → OmegaSemiring.Carrier A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R
  open HalfOrder A R using (half≤1; half-twice)
  open SetoidReasoning setoid

  module _
    (F-cong : ∀ {s t} → s ≈ t → F s ≈ F t)
    (F-mono : ∀ {s t} → s ≤ t → F s ≤ F t)
    (F-1 : F 1# ≈ 1#)
    (FL : ∀ s → s ≤ 1# → F (half * s) ≈ half * Z s + half * F s)
    (ZL : ∀ s → s ≤ 1# → Z s ≤ F 0#)
    (Z0 : Z 0# ≤ 0#)
    (FR : ∀ s → s ≤ 1# → F (half + half * s) ≈ half * F s + half * 1#)
    where

    hp-half : ∀ n → half * hp n ≈ hp (ℕ.suc n)
    hp-half n = begin
      half * hp n                                ≈⟨ *-cong refl (sym (hp-double n)) ⟩
      half * (hp (ℕ.suc n) + hp (ℕ.suc n))      ≈⟨ half-twice _ ⟩
      hp (ℕ.suc n) ∎

    -- F 0 = 0
    F0≤half : F 0# ≤ half * F 0#
    F0≤half = ≤-trans (≤-reflexive (trans (F-cong (sym (zeroʳ half))) (FL 0# 0-least)))
      (≤-trans (+-mono (*-mono half Z0) ≤-refl)
        (≤-reflexive (trans (+-cong (zeroʳ half) refl) (+-identityˡ _))))

    F0≤hp : ∀ n → F 0# ≤ hp n
    F0≤hp ℕ.zero = ≤-trans (F-mono 0-least) (≤-reflexive (trans F-1 (sym hp-zero)))
    F0≤hp (ℕ.suc n) = ≤-trans F0≤half (≤-trans (*-mono half (F0≤hp n)) (≤-reflexive (hp-half n)))

    F0≈0 : F 0# ≈ 0#
    F0≈0 = ≤-antisym (arch (λ n → ≤-trans (F0≤hp n) (≤-reflexive (sym (+-identityˡ _))))) 0-least

    Z≈0 : ∀ s → s ≤ 1# → Z s ≈ 0#
    Z≈0 s s≤1 = ≤-antisym (≤-trans (ZL s s≤1) (≤-reflexive F0≈0)) 0-least

    -- the fixed points of F
    G : ∣A∣ → Set₁
    G x = x ≤ 1# × F x ≈ x

    G-0 : G 0#
    G-0 = 0-least , F0≈0

    G-1 : G 1#
    G-1 = ≤-refl , F-1

    G-L : ∀ {s} → G s → G (half * s)
    G-L {s} (s≤1 , Fs) = ≤-trans (*-mono half s≤1) (≤-trans (≤-reflexive (*-identityʳ half)) half≤1) ,
      trans (FL s s≤1) (trans (+-cong (trans (*-cong refl (Z≈0 s s≤1)) (zeroʳ half)) (*-cong refl Fs)) (+-identityˡ _))

    G-R : ∀ {s} → G s → G (half + half * s)
    G-R {s} (s≤1 , Fs) = ≤-trans (+-mono ≤-refl (*-mono half s≤1))
        (≤-trans (≤-reflexive (+-cong refl (*-identityʳ half))) (≤-reflexive half+half)) ,
      trans (FR s s≤1) (trans (+-cong (*-cong refl Fs) (*-identityʳ half)) (+-comm _ _))

    -- ½ + ½s = t for some s ≤ 1, when ½ ≤ t ≤ 1
    upper-half : ∀ t → half ≤ t → t ≤ 1# → Σ ∣A∣ (λ s → s ≤ 1# × half + half * s ≈ t)
    upper-half t h≤t t≤1 with complement t≤1
    ... | u , tu = s , s≤1 , eq
      where
        u≤h : u ≤ half
        u≤h = cancel≤ half≤1 (≤-trans (+-mono h≤t ≤-refl) (≤-reflexive (trans tu (sym half+half))))
        u≤1 : u ≤ 1#
        u≤1 = ≤-trans u≤h half≤1
        uu≤1 : u + u ≤ 1#
        uu≤1 = ≤-trans (+-mono u≤h u≤h) (≤-reflexive half+half)
        s = proj₁ (complement uu≤1)
        us : (u + u) + s ≈ 1#
        us = proj₂ (complement uu≤1)
        s≤1 : s ≤ 1#
        s≤1 = ≤-trans ≤-+ʳ (≤-reflexive (trans (+-comm s (u + u)) us))
        -- u + ½ s = ½
        uh : u + half * s ≈ half
        uh = begin
          u + half * s                     ≈⟨ +-cong (sym (half-twice u)) refl ⟩
          half * (u + u) + half * s        ≈⟨ sym (distribˡ half (u + u) s) ⟩
          half * ((u + u) + s)             ≈⟨ *-cong refl us ⟩
          half * 1#                        ≈⟨ *-identityʳ half ⟩
          half ∎
        eq : half + half * s ≈ t
        eq = cancel u≤1 (begin
          u + (half + half * s)   ≈⟨ sym (+-assoc u half (half * s)) ⟩
          (u + half) + half * s   ≈⟨ +-cong (+-comm u half) refl ⟩
          (half + u) + half * s   ≈⟨ +-assoc half u (half * s) ⟩
          half + (u + half * s)   ≈⟨ +-cong refl uh ⟩
          half + half             ≈⟨ half+half ⟩
          1#                      ≈⟨ sym (trans (+-comm u t) tu) ⟩
          u + t ∎)

    -- squeezing t between two fixed points 2⁻ⁿ apart
    approx : ∀ n t → t ≤ 1# → Σ ∣A∣ (λ d → Σ ∣A∣ (λ d′ →
      G d × G d′ × d ≤ t × t ≤ d′ × d′ ≤ d + hp n))
    approx ℕ.zero t t≤1 = 0# , 1# , G-0 , G-1 , 0-least , t≤1 ,
      ≤-reflexive (sym (trans (+-identityˡ _) hp-zero))
    approx (ℕ.suc n) t t≤1 with tot t
    ... | inj₁ t≤h with approx n (t + t) (≤-trans (+-mono t≤h t≤h) (≤-reflexive half+half))
    ...   | d , d′ , Gd , Gd′ , d≤s , s≤d′ , gap =
      half * d , half * d′ , G-L Gd , G-L Gd′
        , ≤-trans (*-mono half d≤s) (≤-reflexive (half-twice t))
        , ≤-trans (≤-reflexive (sym (half-twice t))) (*-mono half s≤d′)
        , ≤-trans (*-mono half gap)
            (≤-reflexive (trans (distribˡ half d (hp n)) (+-cong refl (hp-half n))))
    approx (ℕ.suc n) t t≤1 | inj₂ h≤t with upper-half t h≤t t≤1
    ... | s , s≤1 , eq with approx n s s≤1
    ...   | d , d′ , Gd , Gd′ , d≤s , s≤d′ , gap =
      half + half * d , half + half * d′ , G-R Gd , G-R Gd′
        , ≤-trans (+-mono ≤-refl (*-mono half d≤s)) (≤-reflexive eq)
        , ≤-trans (≤-reflexive (sym eq)) (+-mono ≤-refl (*-mono half s≤d′))
        , ≤-trans (+-mono ≤-refl (*-mono half gap))
            (≤-reflexive (begin
              half + half * (d + hp n)             ≈⟨ +-cong refl (distribˡ half d (hp n)) ⟩
              half + (half * d + half * hp n)      ≈⟨ +-cong refl (+-cong refl (hp-half n)) ⟩
              half + (half * d + hp (ℕ.suc n))     ≈⟨ sym (+-assoc half (half * d) (hp (ℕ.suc n))) ⟩
              (half + half * d) + hp (ℕ.suc n) ∎))

    -- F t = t
    selfSimilar : ∀ t → t ≤ 1# → F t ≈ t
    selfSimilar t t≤1 = ≤-antisym
      (arch (λ n → case approx n t t≤1 of λ
        { (d , d′ , Gd , Gd′ , d≤t , t≤d′ , gap) →
          ≤-trans (F-mono t≤d′) (≤-trans (≤-reflexive (proj₂ Gd′)) (≤-trans gap (+-mono d≤t ≤-refl))) }))
      (arch (λ n → case approx n t t≤1 of λ
        { (d , d′ , Gd , Gd′ , d≤t , t≤d′ , gap) →
          ≤-trans t≤d′ (≤-trans gap (≤-trans (+-mono (≤-reflexive (sym (proj₂ Gd))) ≤-refl)
                                             (+-mono (F-mono d≤t) ≤-refl))) }))
