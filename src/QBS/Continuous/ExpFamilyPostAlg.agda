{-# OPTIONS --safe --without-K #-}

-- Ring algebra of conjugate exponents (used by `Continuous/ExpFamilyPost`), over any commutative
-- ring R (used at `Signed.signedRing`, the values of the natural-parameter and log-partition tests at a point):
--   * `·-cong`, `·-+V`: the dot product is a congruence and is additive in its first argument;
--   * `expo χ ν e a = χ · e − ν a` (with ν a = `scaleA ν 1# * a`), the conjugate exponent ⟨χ, η(θ)⟩ − ν A(θ) at a
--     point θ where η(θ) = e and A(θ) = a, with `expo-cong`;
--   * `expo-update`: expo χ ν + expo s N ≈ expo (χ + s) (ν + N), the conjugate update;
--   * `expo-zero`: the exponent of an empty sample is 0; `expo-draw`: adding one draw t, with exponent t · e − a.
-- Route: `SgLinAlg.Σ-+` and `Σ-cong` for the dot product; `ExpFamAlg.scaleA-+` for ν + N; stdlib `interchange` and
-- `⁻¹-∙-comm` (`shape`) for the rearrangement of the four summands.
module QBS.Continuous.ExpFamilyPostAlg where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as Nat

open import Algebra.Properties.CommutativeSemigroup using (interchange)
import Algebra.Properties.AbelianGroup as AbelianGroupProps
import Algebra.Properties.Group as GroupProps
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Analysis.ExpFamAlg using (module ExpFamAlg)

module ExpFamilyPostAlg {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R
    using ( Carrier; _≈_; _+_; _*_; -_; 0#; 1#; refl; sym; trans; setoid; +-cong; +-congʳ; *-cong; *-congʳ; -‿cong
          ; distribʳ; *-identityˡ; zeroˡ; +-identityʳ; +-commutativeSemigroup; +-abelianGroup; +-group )
  open SgLinAlg R using (Vec; _≈V_; _+V_; _·_; Σ-cong; Σ-+; Σ-0)
  open ExpFamAlg R using (scaleA; scaleA-+)
  open AbelianGroupProps +-abelianGroup using (⁻¹-∙-comm)
  open GroupProps +-group using (ε⁻¹≈ε)
  open SetoidReasoning setoid

  ·-cong : ∀ {k} {a a′ b b′ : Vec k} → a ≈V a′ → b ≈V b′ → a · b ≈ a′ · b′
  ·-cong {k} ha hb = Σ-cong k (λ i → *-cong (ha i) (hb i))

  ·-+V : ∀ {k} (a b e : Vec k) → (a +V b) · e ≈ a · e + b · e
  ·-+V {k} a b e = trans (Σ-cong k (λ i → distribʳ (e i) (a i) (b i))) (Σ-+ k _ _)

  -- the four-summand rearrangement shared by `expo-update` and `expo-draw`
  shape : ∀ x y z w → (x + - y) + (z + - w) ≈ (x + z) + - (y + w)
  shape x y z w = trans (interchange +-commutativeSemigroup x (- y) z (- w)) (+-cong refl (⁻¹-∙-comm y w))

  -- the conjugate exponent ⟨χ, e⟩ − ν a
  expo : ∀ {k} → Vec k → ℕ → Vec k → Carrier → Carrier
  expo χ ν e a = χ · e + - (scaleA ν 1# * a)

  expo-cong : ∀ {k} {χ χ′ : Vec k} ν e a → χ ≈V χ′ → expo χ ν e a ≈ expo χ′ ν e a
  expo-cong ν e a h = +-congʳ (·-cong h (λ _ → refl))

  expo-update : ∀ {k} (χ s : Vec k) ν N e a → expo χ ν e a + expo s N e a ≈ expo (χ +V s) (ν Nat.+ N) e a
  expo-update χ s ν N e a = begin
    expo χ ν e a + expo s N e a                           ≈⟨ shape (χ · e) _ (s · e) _ ⟩
    (χ · e + s · e) + - (scaleA ν 1# * a + scaleA N 1# * a) ≈⟨ +-cong (sym (·-+V χ s e)) (-‿cong (sym ν+N)) ⟩
    expo (χ +V s) (ν Nat.+ N) e a                          ∎
    where ν+N = trans (*-congʳ (scaleA-+ ν N 1#)) (distribʳ a _ _)

  expo-zero : ∀ {k} (e : Vec k) a → expo (λ _ → 0#) 0 e a ≈ 0#
  expo-zero {k} e a = begin
    (λ _ → 0#) · e + - (0# * a) ≈⟨ +-cong (trans (Σ-cong k (λ i → zeroˡ (e i))) (Σ-0 k)) (-‿cong (zeroˡ a)) ⟩
    0# + - 0#                   ≈⟨ +-cong refl ε⁻¹≈ε ⟩
    0# + 0#                     ≈⟨ +-identityʳ 0# ⟩
    0#                          ∎

  expo-draw : ∀ {k} (t s : Vec k) N e a → (t · e + - a) + expo s N e a ≈ expo (t +V s) (suc N) e a
  expo-draw t s N e a = begin
    (t · e + - a) + expo s N e a                ≈⟨ shape (t · e) a (s · e) _ ⟩
    (t · e + s · e) + - (a + scaleA N 1# * a)  ≈⟨ +-cong (sym (·-+V t s e)) (-‿cong (sym one+N)) ⟩
    expo (t +V s) (suc N) e a                   ∎
    where one+N = trans (distribʳ a 1# _) (+-congʳ (*-identityˡ a))
