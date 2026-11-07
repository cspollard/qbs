{-# OPTIONS --safe --without-K #-}

-- Where an integrable test is infinite nothing is seen by the integral (an integrable test is finite almost everywhere).
-- For a test g on X with ∫ g finite:
--   * `finχ g`: the indicator of {x | g x is bounded by a rational} (`indH` after g), with `finχ-in`/`finχ-out`;
--   * `∫-infχ`: the complementary indicator integrates to 0;  `∫-null`: so does u · [g = ∞] for every test u;
--   * `∫-off-inf`: tests that agree wherever g is finite have the same integral;  `∫-fin-cut`: ∫ (finχ g · u) ≈ ∫ u.
-- Route: k · [g = ∞] ≤ g for every k, so k · ∫ [g = ∞] ≤ ∫ g ≤ N for all k, which forces ∫ [g = ∞] = 0 (`zero-of`:
-- multiply k = 2ᴺ⁺ʲ by ½ᴺ⁺ʲ and compare with ½ʲ, then `Arch.arch`); u · [g = ∞] is the supremum of [g = ∞] · (u ⊓ j)
-- (`SupTest.∫ᴹ-sup`, `Fatou.supMin`); pointwise u ≈ finχ g · u + [g = ∞] · u by excluded middle on finiteness of g x.
-- Borel: {r | BndQ (α r)} is ⋃_n {r | n ∉ α r}, the complement of a level set (`Meas`).
module QBS.Continuous.NullInf where

open import Level using (lift)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _^_) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Core using (Borel; ⋃; compl)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (Cut; module Cut; unionC; _⊑_; mk⊑; module _⊑_; ⊑-trans; union-ub; union-lub)
open import QBS.Analysis.LowerRealsMin using (_⊓_)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.RationalLemmas using (≃-refl; <-irrefl; <-≤-trans; ≤-or->; nat-bound) renaming (nat to natℚ)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.SupTest using (module SupTest)
open import QBS.Continuous.Fatou using (module Fatou)

open Cut using (mem; down)
open _⊑_ using (ap)

-- the minimum with a constant lies below the constant
⊓-rb : ∀ x y → (x ⊓ y) ⊑ y
⊓-rb x y = mk⊑ (λ q m → proj₂ m)

module NullInf (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; *-assoc; *-comm; *-cong; *-identityˡ; *-identityʳ;
    *-mono; +-identityˡ; +-identityʳ; ≤-trans; ≤-reflexive; ≤-antisym; 0-least; zeroˡ; zeroʳ; +-cong) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half; arch) renaming (half+half to hh)
  open Half A half hh using (hp)
  open BoundedCancel A half hh using (nat-mono; suc≤2^; 2^-suc; half-nat)
  open Weights (lemOf lem₁) using (WQ; constW)
  open Meas (lemOf lem₁) using (Meas)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open Intervals (lemOf lem₁) using (indH; tv-in; tv-out)
  open Product (lemOf lem₁) using (cmul)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX)
  open SupTest (lemOf lem₁) using (supH; supH-pt; ∫ᴹ-monoX; ∫ᴹ-sup)
  open Fatou lem₁ using (minH; minH-pt; minH-inc; supMin)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- 2ᵐ copies of ½ᵐ make 1, and k · E ≤ N for all k gives E = 0

  nat-2 : ∀ m → nat (2 ^ suc m) ≈ nat (2 ^ m +ℕ 2 ^ m)
  nat-2 m = subst (λ i → nat (2 ^ suc m) ≈ nat i) (2^-suc m) refl

  pow-hp : ∀ m j → nat (2 ^ m) * hp (m +ℕ j) ≈ hp j
  pow-hp zero j = trans (*-cong (+-identityʳ 1#) refl) (*-identityˡ _)
  pow-hp (suc m) j = trans (*-cong (nat-2 m) refl) (trans (sym (*-assoc _ _ _))
    (trans (*-cong (*-comm _ _) refl) (trans (*-cong (half-nat (2 ^ m)) refl) (pow-hp m j))))

  pow-hp0 : ∀ m → nat (2 ^ m) * hp m ≈ 1#
  pow-hp0 m = subst (λ i → nat (2 ^ m) * hp i ≈ 1#) (ℕP.+-identityʳ m) (pow-hp m 0)

  -- E ≤ ½ʲ from 2ᴺ⁺ʲ · E ≤ N ≤ 2ᴺ
  tiny : ∀ E N j → nat (2 ^ (N +ℕ j)) * E ≤ nat N → E ≤ hp j
  tiny E N j h = ≤-trans (≤-reflexive (trans (sym (*-identityˡ E)) (trans (*-cong (sym (pow-hp0 m)) refl)
      (trans (*-cong (*-comm _ _) refl) (*-assoc _ _ _)))))
    (≤-trans (*-mono (hp m) (≤-trans h (nat-mono (ℕP.≤-trans (ℕP.n≤1+n N) (suc≤2^ N)))))
      (≤-reflexive (trans (*-comm _ _) (pow-hp N j))))
    where m = N +ℕ j

  zero-of : ∀ E N → (∀ k → nat k * E ≤ nat N) → E ≈ 0#
  zero-of E N h = ≤-antisym (arch (λ j → ≤-trans (tiny E N j (h _)) (≤-reflexive (sym (+-identityˡ _))))) 0-least

  ----------------------------------------------------------------------------
  -- bounded by a rational ⟺ some natural number is not in the cut

  FinP : ∣A∣ → Set
  FinP x = Σ ℕ (λ n → mem x (natℚ n) → ⊥)

  bnd⇒fin : ∀ {t} → BndQ t → FinP t
  bnd⇒fin (M , bd) = proj₁ (nat-bound M) , λ m → <-irrefl ≃-refl (<-≤-trans (bd _ m) (proj₂ (nat-bound M)))

  fin⇒bnd : ∀ {t} → FinP t → BndQ t
  fin⇒bnd {t} (n , nm) = natℚ n , λ r m → go r m (≤-or-> (natℚ n) r)
    where
      go : ∀ r → mem t r → _ → _
      go r m (inj₁ le) = ⊥-elim (nm (down t le m))
      go r m (inj₂ lt) = lt

  FinP-resp : ∀ {x y} → x ≈ y → FinP x → FinP y
  FinP-resp e (n , nm) = n , λ m → nm (ap (proj₂ e) _ m)

  fin-borel : ∀ {α : R₁ → ∣A∣} → Meas α → Borel (λ c → FinP (α (lift c)))
  fin-borel m = ⋃ (λ n → compl (m (natℚ n)))

  -- an unbounded cut contains every rational
  all-in : ∀ {t} → (BndQ t → ⊥) → ∀ q → mem t q
  all-in {t} nb q with lemOf lem₁ (mem t q)
  ... | inj₁ yes = yes
  ... | inj₂ no = ⊥-elim (nb (q , λ r m → go r m (≤-or-> q r)))
    where
      go : ∀ r → mem t r → _ → _
      go r m (inj₁ le) = ⊥-elim (no (down t le m))
      go r m (inj₂ lt) = lt

  module _ {X : QBS S} where

    -- [g x finite] and [g x = ∞]
    finχ infχ : Hom S X WQ → Hom S X WQ
    finχ g = _∘H_ S {X} {WQ} {WQ} (indH FinP FinP-resp fin-borel) g
    infχ g = _∘H_ S {X} {WQ} {WQ} (indH (λ x → FinP x → ⊥) (λ e f n → f (FinP-resp (OmegaSemiring.sym A e) n))
      (λ m → compl (fin-borel m))) g

    finχ-in : ∀ g x → BndQ (map g ⟨$⟩ x) → map (finχ g) ⟨$⟩ x ≈ 1#
    finχ-in g x b = tv-in (bnd⇒fin {map g ⟨$⟩ x} b)

    finχ-out : ∀ g x → (BndQ (map g ⟨$⟩ x) → ⊥) → map (finχ g) ⟨$⟩ x ≈ 0#
    finχ-out g x nb = tv-out (λ f → nb (fin⇒bnd {map g ⟨$⟩ x} f))

    infχ-in : ∀ g x → (BndQ (map g ⟨$⟩ x) → ⊥) → map (infχ g) ⟨$⟩ x ≈ 1#
    infχ-in g x nb = tv-in (λ f → nb (fin⇒bnd {map g ⟨$⟩ x} f))

    infχ-out : ∀ g x → BndQ (map g ⟨$⟩ x) → map (infχ g) ⟨$⟩ x ≈ 0#
    infχ-out g x b = tv-out (λ nf → nf (bnd⇒fin {map g ⟨$⟩ x} b))

    -- k · [g = ∞] ≤ g
    inf-le : ∀ g k x → nat k * (map (infχ g) ⟨$⟩ x) ≤ map g ⟨$⟩ x
    inf-le g k x with lemOf lem₁ (BndQ (map g ⟨$⟩ x))
    ... | inj₁ b = ≤-trans (≤-reflexive (trans (*-cong refl (infχ-out g x b)) (zeroʳ _))) 0-least
    ... | inj₂ nb = ≤-trans (≤-reflexive (trans (*-cong refl (infχ-in g x nb)) (*-identityʳ _)))
        (mk⊑ (λ q _ → all-in {map g ⟨$⟩ x} nb q))

    ∫-infχ : ∀ (p : C.Pre (XW X)) g → Bnd (∫ᴹ {X} p g) → ∫ᴹ {X} p (infχ g) ≈ 0#
    ∫-infχ p g (N , hN) = zero-of _ N (λ k → ≤-trans (≤-reflexive (sym (cmul p (nat k) (infχ g))))
      (≤-trans (∫ᴹ-monoX p {mulH {X} (constW {X} (nat k)) (infχ g)} {g} (inf-le g k)) hN))

    -- the truncations [g = ∞] · (u ⊓ n), increasing to [g = ∞] · u
    hN : Hom S X WQ → Hom S X WQ → ℕ → Hom S X WQ
    hN g u n = mulH {X} (infχ g) (minH {X} n u)

    hN-inc : ∀ g u n x → map (hN g u n) ⟨$⟩ x ≤ map (hN g u (suc n)) ⟨$⟩ x
    hN-inc g u n x = *-mono _ (minH-inc u n x)

    union-≈ : ∀ {a b : ℕ → Cut} → (∀ n → a n ≈ b n) → unionC a ≈ unionC b
    union-≈ {a} {b} e = union-lub a (λ n → ⊑-trans (proj₁ (e n)) (union-ub b n))
      , union-lub b (λ n → ⊑-trans (proj₂ (e n)) (union-ub a n))

    -- where g is finite everything is 0, where it is infinite the truncations converge to u
    hN-sup : ∀ g u x → map (supH {X} (hN g u)) ⟨$⟩ x ≈ map (mulH {X} (infχ g) u) ⟨$⟩ x
    hN-sup g u x with lemOf lem₁ (BndQ (map g ⟨$⟩ x))
    ... | inj₁ b = trans (supH-pt (hN g u) x) (trans (union-lub _ (λ n → ≤-reflexive (z n)) , 0-least)
        (sym (trans (*-cong (infχ-out g x b) refl) (zeroˡ _))))
      where z : ∀ n → map (hN g u n) ⟨$⟩ x ≈ 0#
            z n = trans (*-cong (infχ-out g x b) refl) (zeroˡ _)
    ... | inj₂ nb = trans (supH-pt (hN g u) x) (trans (union-≈ (λ n → trans (*-cong (infχ-in g x nb) refl) (*-identityˡ _)))
        (trans (sym (supH-pt (λ n → minH {X} n u) x)) (trans (supMin u x)
          (sym (trans (*-cong (infχ-in g x nb) refl) (*-identityˡ _))))))

    hN-int : ∀ (p : C.Pre (XW X)) g u → Bnd (∫ᴹ {X} p g) → ∀ n → ∫ᴹ {X} p (hN g u n) ≤ 0#
    hN-int p g u bg n = ≤-trans (∫ᴹ-monoX p {hN g u n} {mulH {X} (constW {X} (nat n)) (infχ g)} le)
      (≤-reflexive (trans (cmul p (nat n) (infχ g)) (trans (*-cong refl (∫-infχ p g bg)) (zeroʳ _))))
      where le : ∀ x → map (hN g u n) ⟨$⟩ x ≤ nat n * (map (infχ g) ⟨$⟩ x)
            le x = ≤-trans (*-mono _ (≤-trans (≤-reflexive (minH-pt n u x)) (⊓-rb _ _))) (≤-reflexive (*-comm _ _))

    ∫-null : ∀ (p : C.Pre (XW X)) g u → Bnd (∫ᴹ {X} p g) → ∫ᴹ {X} p (mulH {X} (infχ g) u) ≈ 0#
    ∫-null p g u bg = trans (sym (∫ᴹ-cong p {supH {X} (hN g u)} {mulH {X} (infχ g) u} (hN-sup g u)))
      (trans (∫ᴹ-sup p (hN g u) (hN-inc g u)) (union-lub (λ n → ∫ᴹ {X} p (hN g u n)) (hN-int p g u bg) , 0-least))

    -- u = finχ g · u + [g = ∞] · u
    split-pt : ∀ g u x → map (addX {X} (mulH {X} (finχ g) u) (mulH {X} (infχ g) u)) ⟨$⟩ x ≈ map u ⟨$⟩ x
    split-pt g u x with lemOf lem₁ (BndQ (map g ⟨$⟩ x))
    ... | inj₁ b = trans (+-cong (*-cong (finχ-in g x b) refl) (*-cong (infχ-out g x b) refl))
        (trans (+-cong (*-identityˡ _) (zeroˡ _)) (+-identityʳ _))
    ... | inj₂ nb = trans (+-cong (*-cong (finχ-out g x nb) refl) (*-cong (infχ-in g x nb) refl))
        (trans (+-cong (zeroˡ _) (*-identityˡ _)) (+-identityˡ _))

    ∫-fin-cut : ∀ (p : C.Pre (XW X)) g u → Bnd (∫ᴹ {X} p g) → ∫ᴹ {X} p (mulH {X} (finχ g) u) ≈ ∫ᴹ {X} p u
    ∫-fin-cut p g u bg = trans (sym (+-identityʳ _)) (trans (+-cong refl (sym (∫-null p g u bg)))
      (trans (sym (∫ᴹ-addX p (mulH {X} (finχ g) u) (mulH {X} (infχ g) u))) (∫ᴹ-cong p (split-pt g u))))

    ∫-off-inf : ∀ (p : C.Pre (XW X)) g u v → Bnd (∫ᴹ {X} p g) →
      (∀ x → BndQ (map g ⟨$⟩ x) → map u ⟨$⟩ x ≈ map v ⟨$⟩ x) → ∫ᴹ {X} p u ≈ ∫ᴹ {X} p v
    ∫-off-inf p g u v bg ag = trans (sym (∫-fin-cut p g u bg))
      (trans (∫ᴹ-cong p {mulH {X} (finχ g) u} {mulH {X} (finχ g) v} cut) (∫-fin-cut p g v bg))
      where
        cut : ∀ x → map (mulH {X} (finχ g) u) ⟨$⟩ x ≈ map (mulH {X} (finχ g) v) ⟨$⟩ x
        cut x with lemOf lem₁ (BndQ (map g ⟨$⟩ x))
        ... | inj₁ b = *-cong refl (ag x b)
        ... | inj₂ nb = trans (trans (*-cong (finχ-out g x nb) refl) (zeroˡ _))
            (sym (trans (*-cong (finχ-out g x nb) refl) (zeroˡ _)))
