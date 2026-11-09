{-# OPTIONS --safe --without-K #-}

-- Helper for `MonoTest`: an up-set V of [0,∞] (respecting ≈) pulls threshold-measurable maps back to Borel sets.
-- Let E be the intersection of the cuts in V, as a set of rationals (it need not be a cut).  Then {x | E ⊆ x} ⊇ V
-- and V ⊇ {x | E ⊆ x, x ⊄ E}, so V differs from {x | E ⊆ x} only at the points with x = E, where V is constant;
-- both {x | E ⊆ x} and {x | x ⊆ E} are Borel along measurable probes (countable intersections over the rationals).
module QBS.Continuous.MonoTestAlg where

open import Level using (lift)
open import Function.Base using (case_of_)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Rational.Unnormalised.Base using (ℚᵘ)
open import Data.Rational.Unnormalised.Properties using (≤-total)

open import QBS.Classical using (LEM₁)
open import QBS.Borel.Core using (Borel; compl; inter₂; resp; ⊤-borel)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (module Cut; mk⊑)
open Cut using (mem; down)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)

module MonoAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_) renaming (Carrier to ∣A∣)
  open Meas (lemOf lem₁) using (Meas; all-enum; imp-borel)

  -- a `Set`-valued copy of a `Set₁` proposition
  small : (P : Set₁) → Σ Set (λ Q → (Q → P) × (P → Q))
  small P with lem₁ P
  ... | inj₁ p = ⊤ , (λ _ → p) , (λ _ → tt)
  ... | inj₂ np = ⊥ , (λ b → ⊥-elim b) , (λ p → ⊥-elim (np p))

  module _ (V : ∣A∣ → Set) (Vcong : ∀ {x y} → x ≈ y → V x → V y)
           (Vup : ∀ {x y} → x ≤ y → V x → V y) where
    -- E, the intersection of the cuts in V, and its `Set`-valued copy
    E : ℚᵘ → Set₁
    E ρ = ∀ y → V y → mem y ρ

    Ê : ℚᵘ → Set
    Ê ρ = proj₁ (small (E ρ))

    -- the cut-like sets E ⊆ x and x ⊆ E, and the point x = E is in V
    G : ∣A∣ → Set
    G x = ∀ ρ → Ê ρ → mem x ρ

    S : ∣A∣ → Set₁
    S x = ∀ ρ → mem x ρ → E ρ

    P : Set₁
    P = Σ ∣A∣ (λ x → (∀ ρ → E ρ → mem x ρ) × S x × V x)

    L : ∣A∣ → Set
    L x = ∀ ρ → mem x ρ → Ê ρ

    toE : ∀ ρ → Ê ρ → E ρ
    toE ρ = proj₁ (proj₂ (small (E ρ)))

    fromE : ∀ ρ → E ρ → Ê ρ
    fromE ρ = proj₂ (proj₂ (small (E ρ)))

    V-G : ∀ {x} → V x → G x
    V-G Vx ρ ê = toE ρ ê _ Vx

    V-L : ∀ {x} → V x → (P → ⊥) → L x → ⊥
    V-L Vx nP l = nP (_ , (λ ρ e → e _ Vx) , (λ ρ m → toE ρ (l ρ m)) , Vx)

    -- a rational in x but not in E gives a member of V below x
    below : ∀ {x} → (S x → ⊥) → Σ ℚᵘ (λ p → mem x p × (E p → ⊥))
    below {x} nS with lem₁ (Σ ℚᵘ (λ p → mem x p × (E p → ⊥)))
    ... | inj₁ w = w
    ... | inj₂ no = ⊥-elim (nS (λ ρ m → case lem₁ (E ρ) of λ
      { (inj₁ e) → e ; (inj₂ ne) → ⊥-elim (no (ρ , m , ne)) }))

    member : ∀ p → (E p → ⊥) → Σ ∣A∣ (λ y → V y × (mem y p → ⊥))
    member p nE with lem₁ (Σ ∣A∣ (λ y → V y × (mem y p → ⊥)))
    ... | inj₁ w = w
    ... | inj₂ no = ⊥-elim (nE (λ y Vy → case lemOf lem₁ (mem y p) of λ
      { (inj₁ m) → m ; (inj₂ nm) → ⊥-elim (no (y , Vy , nm)) }))

    W : ∀ {x} → (S x → ⊥) → V x
    W {x} nS = case below nS of λ { (p , mx , nE) → case member p nE of λ { (y , Vy , ny) →
      Vup (mk⊑ (λ r my → case ≤-total p r of λ
        { (inj₁ le) → ⊥-elim (ny (down y le my)) ; (inj₂ le) → down x le mx })) Vy } }

    -- the point x = E
    Wp : ∀ {x} → P → G x → V x
    Wp {x} (x′ , i , o , Vx′) g = case lem₁ (S x) of λ
      { (inj₁ s) → Vcong (mk⊑ (λ ρ m → g ρ (fromE ρ (o ρ m))) , mk⊑ (λ ρ m → i ρ (s ρ m))) Vx′
      ; (inj₂ nS) → W nS }

    Wn : ∀ {x} → (L x → ⊥) → V x
    Wn nL = W (λ s → nL (λ ρ m → fromE ρ (s ρ m)))

    Gb : ∀ {h} → Meas h → Borel (λ c → G (h (lift c)))
    Gb {h} m = all-enum (λ ρ c → Ê ρ → mem (h (lift c)) ρ) (λ ρ → imp-borel (Ê ρ) (m ρ))

    Lb : ∀ {h} → Meas h → Borel (λ c → L (h (lift c)))
    Lb {h} m = all-enum (λ ρ c → mem (h (lift c)) ρ → Ê ρ) bimp
      where
        bimp : ∀ ρ → Borel (λ c → mem (h (lift c)) ρ → Ê ρ)
        bimp ρ = case lemOf lem₁ (Ê ρ) of λ
          { (inj₁ e) → resp (λ c → (λ _ _ → e) , (λ _ → tt)) ⊤-borel
          ; (inj₂ ne) → resp (λ c → (λ n mm → ⊥-elim (n mm)) , (λ f mm → ne (f mm))) (compl (m ρ)) }

    -- an up-set of [0,∞] respecting ≈ is Borel along every threshold-measurable probe
    up-borel : ∀ {h} → Meas h → Borel (λ c → V (h (lift c)))
    up-borel {h} m = case lem₁ P of λ
      { (inj₁ p) → resp (λ c → Wp p , V-G) (Gb m)
      ; (inj₂ np) → resp (λ c → (λ { (g , nl) → Wn nl }) , (λ v → V-G v , V-L v np))
                          (inter₂ (Gb m) (compl (Lb m))) }
