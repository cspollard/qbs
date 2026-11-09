{-# OPTIONS --safe --without-K #-}

-- `Bind M`: the one spelling of bind and Kleisli composition for a monad `M`, so that proofs about measures read
-- as monad calculations.  Later code should use it (`open Bind M`) instead of writing `μ ∘ M k ∘ t` by hand.
-- Generic: nothing here mentions products, measures or QBS.
--   `bind k t`     `μ ∘ M k ∘ t`, for `k : X ⇒ M Y` and any `t : Z ⇒ M X` ("t >>= k", with the kernel first)
--   `k ∘ᴷ h`       Kleisli composition `bind k h` of `h : X ⇒ M Y` and `k : Y ⇒ M W`, as a map `X ⇒ M W`
--   laws           `bind-return`, `bind-η`, `bind-η-∘` (unit laws), `bind-assoc` (associativity),
--                  `bind-pre`, `bind-nat`, `bind-map`, `bind-join` (interaction with `∘`, `M`, `μ`), `bind-cong`.
-- It is the vocabulary of `Categories.Category.Construction.Kleisli` without that category: global elements
-- `⊤ ⇒ M X` are bound through kernels `X ⇒ M Y`, and `scaleM a t` of `Statistical` is `bind t (score ∘ a)`.
module QBS.Monad.Bind where

open import Level using (Level)

open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)
import Categories.Morphism.Reasoning as MR

module Bind {o h e} {C : Category o h e} (M : Monad C) where
  open Category C
  open HomReasoning
  open MR C
  private module T = Monad M

  infixr 9 _∘ᴷ_

  bind : ∀ {X Y Z} → X ⇒ T.F.F₀ Y → Z ⇒ T.F.F₀ X → Z ⇒ T.F.F₀ Y
  bind {Y = Y} k t = T.μ.η Y ∘ T.F.F₁ k ∘ t

  -- Kleisli composition: first `h`, then `k`
  _∘ᴷ_ : ∀ {X Y W} → Y ⇒ T.F.F₀ W → X ⇒ T.F.F₀ Y → X ⇒ T.F.F₀ W
  k ∘ᴷ h = bind k h

  bind-cong : ∀ {X Y Z} {k k′ : X ⇒ T.F.F₀ Y} {t t′ : Z ⇒ T.F.F₀ X} →
    k ≈ k′ → t ≈ t′ → bind k t ≈ bind k′ t′
  bind-cong k≈ t≈ = refl⟩∘⟨ T.F.F-resp-≈ k≈ ⟩∘⟨ t≈

  -- right unit: binding through `η` does nothing
  bind-return : ∀ {X Z} (t : Z ⇒ T.F.F₀ X) → bind (T.η.η X) t ≈ t
  bind-return {X} t = cancelˡ T.identityˡ

  -- left unit: binding a returned point is the kernel at that point
  bind-η : ∀ {X Y Z} (k : X ⇒ T.F.F₀ Y) (x : Z ⇒ X) → bind k (T.η.η X ∘ x) ≈ k ∘ x
  bind-η {X} k x = begin
    T.μ.η _ ∘ T.F.F₁ k ∘ T.η.η X ∘ x  ≈⟨ refl⟩∘⟨ extendʳ (T.η.sym-commute k) ⟩
    T.μ.η _ ∘ T.η.η _ ∘ k ∘ x         ≈⟨ cancelˡ T.identityʳ ⟩
    k ∘ x                              ∎

  -- binding a returned kernel is mapping
  bind-η-∘ : ∀ {X Y Z} (f : X ⇒ Y) (t : Z ⇒ T.F.F₀ X) → bind (T.η.η Y ∘ f) t ≈ T.F.F₁ f ∘ t
  bind-η-∘ {X} {Y} f t = begin
    T.μ.η Y ∘ T.F.F₁ (T.η.η Y ∘ f) ∘ t              ≈⟨ refl⟩∘⟨ T.F.homomorphism ⟩∘⟨refl ⟩
    T.μ.η Y ∘ (T.F.F₁ (T.η.η Y) ∘ T.F.F₁ f) ∘ t     ≈⟨ refl⟩∘⟨ assoc ⟩
    T.μ.η Y ∘ T.F.F₁ (T.η.η Y) ∘ T.F.F₁ f ∘ t       ≈⟨ cancelˡ T.identityˡ ⟩
    T.F.F₁ f ∘ t                                      ∎

  -- associativity: bind through `k`, then through `h`, is bind through the Kleisli composite
  bind-assoc : ∀ {X Y W Z} (h : Y ⇒ T.F.F₀ W) (k : X ⇒ T.F.F₀ Y) (t : Z ⇒ T.F.F₀ X) →
    bind h (bind k t) ≈ bind (bind h k) t
  bind-assoc {W = W} h k t = begin
    T.μ.η W ∘ T.F.F₁ h ∘ T.μ.η _ ∘ T.F.F₁ k ∘ t
      ≈⟨ refl⟩∘⟨ extendʳ (T.μ.sym-commute h) ⟩
    T.μ.η W ∘ T.μ.η _ ∘ T.F.F₁ (T.F.F₁ h) ∘ T.F.F₁ k ∘ t
      ≈⟨ sym-assoc ⟩
    (T.μ.η W ∘ T.μ.η _) ∘ T.F.F₁ (T.F.F₁ h) ∘ T.F.F₁ k ∘ t
      ≈⟨ T.sym-assoc ⟩∘⟨refl ⟩
    (T.μ.η W ∘ T.F.F₁ (T.μ.η W)) ∘ T.F.F₁ (T.F.F₁ h) ∘ T.F.F₁ k ∘ t
      ≈⟨ assoc ⟩
    T.μ.η W ∘ T.F.F₁ (T.μ.η W) ∘ T.F.F₁ (T.F.F₁ h) ∘ T.F.F₁ k ∘ t
      ≈⟨ refl⟩∘⟨ pullˡ (⟺ T.F.homomorphism) ⟩
    T.μ.η W ∘ T.F.F₁ (T.μ.η W ∘ T.F.F₁ h) ∘ T.F.F₁ k ∘ t
      ≈⟨ refl⟩∘⟨ pullˡ (⟺ T.F.homomorphism) ⟩
    T.μ.η W ∘ T.F.F₁ ((T.μ.η W ∘ T.F.F₁ h) ∘ k) ∘ t
      ≈⟨ refl⟩∘⟨ T.F.F-resp-≈ assoc ⟩∘⟨refl ⟩
    T.μ.η W ∘ T.F.F₁ (T.μ.η W ∘ T.F.F₁ h ∘ k) ∘ t ∎

  -- Kleisli composition is associative
  ∘ᴷ-assoc : ∀ {X Y W V} (j : W ⇒ T.F.F₀ V) (k : Y ⇒ T.F.F₀ W) (h : X ⇒ T.F.F₀ Y) →
    (j ∘ᴷ k) ∘ᴷ h ≈ j ∘ᴷ (k ∘ᴷ h)
  ∘ᴷ-assoc j k h = ⟺ (bind-assoc j k h)

  -- precomposition goes inside the bind
  bind-pre : ∀ {X Y Z Z′} (k : X ⇒ T.F.F₀ Y) (t : Z ⇒ T.F.F₀ X) (s : Z′ ⇒ Z) →
    bind k t ∘ s ≈ bind k (t ∘ s)
  bind-pre k t s = begin
    (T.μ.η _ ∘ T.F.F₁ k ∘ t) ∘ s  ≈⟨ assoc ⟩
    T.μ.η _ ∘ (T.F.F₁ k ∘ t) ∘ s  ≈⟨ refl⟩∘⟨ assoc ⟩
    T.μ.η _ ∘ T.F.F₁ k ∘ t ∘ s    ∎

  -- mapping after a bind is binding through the mapped kernel
  bind-nat : ∀ {X Y W Z} (f : Y ⇒ W) (k : X ⇒ T.F.F₀ Y) (t : Z ⇒ T.F.F₀ X) →
    T.F.F₁ f ∘ bind k t ≈ bind (T.F.F₁ f ∘ k) t
  bind-nat {W = W} f k t = begin
    T.F.F₁ f ∘ T.μ.η _ ∘ T.F.F₁ k ∘ t                   ≈⟨ extendʳ (T.μ.sym-commute f) ⟩
    T.μ.η W ∘ T.F.F₁ (T.F.F₁ f) ∘ T.F.F₁ k ∘ t          ≈⟨ refl⟩∘⟨ pullˡ (⟺ T.F.homomorphism) ⟩
    T.μ.η W ∘ T.F.F₁ (T.F.F₁ f ∘ k) ∘ t                  ∎

  -- mapping the measure before a bind is precomposing the kernel
  bind-map : ∀ {X X′ Y Z} (k : X′ ⇒ T.F.F₀ Y) (f : X ⇒ X′) (t : Z ⇒ T.F.F₀ X) →
    bind k (T.F.F₁ f ∘ t) ≈ bind (k ∘ f) t
  bind-map k f t = begin
    T.μ.η _ ∘ T.F.F₁ k ∘ T.F.F₁ f ∘ t   ≈⟨ refl⟩∘⟨ pullˡ (⟺ T.F.homomorphism) ⟩
    T.μ.η _ ∘ T.F.F₁ (k ∘ f) ∘ t         ∎

  -- joining after a bind is binding through the joined kernel
  bind-join : ∀ {X Y Z} (K : X ⇒ T.F.F₀ (T.F.F₀ Y)) (t : Z ⇒ T.F.F₀ X) →
    T.μ.η Y ∘ bind K t ≈ bind (T.μ.η Y ∘ K) t
  bind-join {Y = Y} K t = begin
    T.μ.η Y ∘ T.μ.η _ ∘ T.F.F₁ K ∘ t                     ≈⟨ sym-assoc ⟩
    (T.μ.η Y ∘ T.μ.η _) ∘ T.F.F₁ K ∘ t                   ≈⟨ ⟺ T.assoc ⟩∘⟨refl ⟩
    (T.μ.η Y ∘ T.F.F₁ (T.μ.η Y)) ∘ T.F.F₁ K ∘ t          ≈⟨ assoc ⟩
    T.μ.η Y ∘ T.F.F₁ (T.μ.η Y) ∘ T.F.F₁ K ∘ t            ≈⟨ refl⟩∘⟨ pullˡ (⟺ T.F.homomorphism) ⟩
    T.μ.η Y ∘ T.F.F₁ (T.μ.η Y ∘ K) ∘ t                    ∎
