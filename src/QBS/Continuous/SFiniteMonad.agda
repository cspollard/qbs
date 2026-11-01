{-# OPTIONS --safe --without-K #-}

-- The monad structure of the s-finite measures (`Continuous/SFinite`): functor, unit, join and the monad laws.

module QBS.Continuous.SFiniteMonad where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.IntegralMonad using (Integral; MonadData; module Laws)
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (R₁; cantorSource; down)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad using (module Continuous)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import QBS.Classical using (LEM₀)

module SFiniteMonad (lem : LEM₀) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zero⇒)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open UnitInterval A using (AQ)
  open RandomSource S using (Rˢ) renaming (meas-id to measId)
  open SFinite lem
  open WitM
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- a witness for a random family of joins

  module JoinWit {X : QBS S} {β : R₁ → Pre (XW (TQ X))} (w : WitM {TQ X} β) where
    -- the outer weight and the inner measure at the merged parameter
    Ww : R₁ → Cut
    Ww k = proj₁ (map (a w) ⟨$⟩ (evensR k , oddsR k))

    νw : R₁ → Pre (XW X)
    νw k = proj₂ (map (a w) ⟨$⟩ (evensR k , oddsR k))

    w₂ : WitM {X} νw
    w₂ = proj₂ (paJ {TQ X} (a w))

    a₂ : Joint (XW X)
    a₂ = a w₂

    -- the inner measure on u = merge s t, given the merged parameter k = merge r s
    K′ : R₁ → Measure
    K′ k = push {mergeR (oddsR k)} (measurable-merge₁ (lower (oddsR k))) (g w₂ k)

    kK′ : KernelOk K′
    kK′ {h} fh = Fun-ext
      (λ k → I-cong (g w₂ k)
               (λ t → Fun-resp lem fh (lower (mergeR-cong (oddsR-cong (merge-evens k t)) (merge-odds k t)))) _ _)
      (P₁.PF (g w₂) (g-ok w₂) {λ x → h (φ x)} (Fun-pre {h} {φ} fh mφ))
      where
        φ : R₁ → R₁
        φ x = mergeR (oddsR (evensR x)) (oddsR x)
        mφ : Measurable (down φ)
        mφ = measurable-merge (measurable-∘ measurable-evens measurable-odds) measurable-odds

    gK : R₁ → R₁ → Measure
    gK r s = K′ (mergeR r s)

    kgK : ∀ r → KernelOk (gK r)
    kgK r fh = Fun-pre (kK′ fh) (measurable-merge₁ (lower r))

    g′ : R₁ → Measure
    g′ r = bind (g w r) (gK r) (kgK r)

    gok′ : KernelOk g′
    gok′ fh = P₁.PF (g w) (g-ok w) (kK′ fh)

    gpr′ : ∀ r → IsProb (g′ r)
    gpr′ r = IsProb-bind {g w r} {gK r} {kgK r} (g-pr w r)
      (λ s → IsProb-push {mergeR (oddsR (mergeR r s))} (measurable-merge₁ (lower (oddsR (mergeR r s))))
          {g w₂ (mergeR r s)} (g-pr w₂ (mergeR r s)))

    Ww-cong : ∀ {k k′} → k R≈.≈ k′ → Ww k ≈ Ww k′
    Ww-cong ek = proj₁ (Func.cong (map (a w)) (evensR-cong ek , oddsR-cong ek))

    a′ : Joint (XW X)
    a′ = record
      { map = record
          { to = λ p → let k = mergeR (proj₁ p) (evensR (proj₂ p)) ; u = oddsR (proj₂ p) in
              Ww k * proj₁ (map a₂ ⟨$⟩ (k , u)) , proj₂ (map a₂ ⟨$⟩ (k , u))
          ; cong = λ (e₁ , e₂) → let ek = mergeR-cong e₁ (evensR-cong e₂) ; ca = Func.cong (map a₂) (ek , oddsR-cong e₂)
                                 in *-cong (Ww-cong ek) (proj₁ ca) , proj₂ ca }
      ; map-random = λ {γ} (m₁ , m₂) →
          let mκ = measurable-merge m₁ (measurable-∘ m₂ measurable-evens)
              mτ = measurable-∘ m₂ measurable-odds
              pr = map-random a₂ {reassocR ∘ₛ γ} (mκ , mτ)
          in Meas-⊗ {λ x → Ww (mergeR (proj₁ (γ ⟨$⟩ x)) (evensR (proj₂ (γ ⟨$⟩ x))))}
                {λ x → proj₁ (map a₂ ⟨$⟩ (mergeR (proj₁ (γ ⟨$⟩ x)) (evensR (proj₂ (γ ⟨$⟩ x))) , oddsR (proj₂ (γ ⟨$⟩ x))))}
                (Meas-pre {Ww} {λ x → mergeR (proj₁ (γ ⟨$⟩ x)) (evensR (proj₂ (γ ⟨$⟩ x)))} (proj₁ (paJ {TQ X} (a w))) mκ)
                (proj₁ pr)
           , proj₂ pr
      }

    -- the inner integral at the merged parameter, as a parametric function
    module Sec (f : Hom S X WQ) where
      Jσ : R₁ → Cut
      Jσ k = J (g w₂ k) (λ t → φJ {X} a₂ f (mergeR k t))
        (Meas-pre {φJ {X} a₂ f} {mergeR k} (mφJ {X} a₂ f) (measurable-merge₁ (lower k)))

      abstract
        mJσ : Meas Jσ
        mJσ = Meas-Jsec (g w₂) (g-ok w₂) {φJ {X} a₂ f} (mφJ {X} a₂ f)

      Bf : R₁ → R₁ → Cut
      Bf r s = Ww (mergeR r s) * Jσ (mergeR r s)

      abstract
        mBf : ∀ r → Meas (Bf r)
        mBf r = Meas-pre {λ k → Ww k * Jσ k} {mergeR r}
          (Meas-⊗ {Ww} {Jσ} (proj₁ (paJ {TQ X} (a w))) mJσ) (measurable-merge₁ (lower r))

      KP : R₁ → Pre (XW X)
      KP r = kerP {X} a′ g′ gpr′ r

      Gq : R₁ → R₁ → Cut
      Gq k u = (Ww k * proj₁ (map a₂ ⟨$⟩ (k , u))) * (map f ⟨$⟩ proj₂ (map a₂ ⟨$⟩ (k , u)))

      Hq : R₁ → R₁ → Cut
      Hq k u = proj₁ (map a₂ ⟨$⟩ (k , u)) * (map f ⟨$⟩ proj₂ (map a₂ ⟨$⟩ (k , u)))

      Gq-cong : ∀ {k k′ u u′} → k R≈.≈ k′ → u R≈.≈ u′ → Gq k u ≈ Gq k′ u′
      Gq-cong ek eu = let ca = Func.cong (map a₂) (ek , eu) in *-cong (*-cong (Ww-cong ek) (proj₁ ca)) (Func.cong (map f) (proj₂ ca))

      Hq-cong : ∀ {k k′ u u′} → k R≈.≈ k′ → u R≈.≈ u′ → Hq k u ≈ Hq k′ u′
      Hq-cong ek eu = let ca = Func.cong (map a₂) (ek , eu) in *-cong (proj₁ ca) (Func.cong (map f) (proj₂ ca))

      -- the integrand at the second level, rewritten through the splitting of the parameter
      ptt : ∀ r s t → ψ {X} (KP r) f (mergeR (oddsR (mergeR r s)) t)
                      ≈ Ww (mergeR r s) * φJ {X} a₂ f (mergeR (mergeR r s) t)
      ptt r s t = trans
        (Gq-cong (R≈.trans (mergeR-cong (R≈.refl {r}) (merge-evens (oddsR (mergeR r s)) t))
                           (mergeR-cong (R≈.refl {r}) (merge-odds r s)))
                 (merge-odds (oddsR (mergeR r s)) t))
        (trans (*-assoc _ _ _)
          (*-cong refl (sym (Hq-cong (merge-evens (mergeR r s) t) (merge-odds (mergeR r s) t)))))

      -- the right-hand side as an integral over r
      stepC : ∀ r → ∫ᴹ {X} (KP r) f ≈ J (g w r) (Bf r) (mBf r)
      stepC r = trans
        (J-bind (g w r) (gK r) (kgK r) {ψ {X} (KP r) f} (mψ {X} (KP r) f)
           (Meas-J (gK r) (kgK r) {ψ {X} (KP r) f} (mψ {X} (KP r) f)))
        (J-cong (g w r) (Meas-J (gK r) (kgK r) {ψ {X} (KP r) f} (mψ {X} (KP r) f)) (mBf r) (λ s →
          trans (J-push {mergeR (oddsR (mergeR r s))} (measurable-merge₁ (lower (oddsR (mergeR r s)))) (g w₂ (mergeR r s))
                   {ψ {X} (KP r) f} (mψ {X} (KP r) f)
                   (Meas-pre {ψ {X} (KP r) f} {mergeR (oddsR (mergeR r s))} (mψ {X} (KP r) f)
                      (measurable-merge₁ (lower (oddsR (mergeR r s))))))
            (trans (J-cong (g w₂ (mergeR r s)) {λ t → ψ {X} (KP r) f (mergeR (oddsR (mergeR r s)) t)}
                      {λ t → Ww (mergeR r s) * φJ {X} a₂ f (mergeR (mergeR r s) t)}
                      (Meas-pre {ψ {X} (KP r) f} {mergeR (oddsR (mergeR r s))} (mψ {X} (KP r) f)
                         (measurable-merge₁ (lower (oddsR (mergeR r s)))))
                      (Meas-⊗ {λ _ → Ww (mergeR r s)} {λ t → φJ {X} a₂ f (mergeR (mergeR r s) t)}
                         (Meas-const (Ww (mergeR r s)))
                         (Meas-pre {φJ {X} a₂ f} {mergeR (mergeR r s)} (mφJ {X} a₂ f) (measurable-merge₁ (lower (mergeR r s)))))
                      (ptt r s))
                   (J-scale (g w₂ (mergeR r s)) (Ww (mergeR r s)) {λ t → φJ {X} a₂ f (mergeR (mergeR r s) t)}
                      (Meas-pre {φJ {X} a₂ f} {mergeR (mergeR r s)} (mφJ {X} a₂ f) (measurable-merge₁ (lower (mergeR r s))))))))

      -- the left-hand side
      stepA : ∀ r → ∫ᴹ {X} (joinPre {X} (β r)) f ≈ J (g w r) (Bf r) (mBf r)
      stepA r = trans (∫ᴹ-join {X} (β r) f) (trans (w-eq w r (∫ᶠ {X} f))
        (J-cong (g w r) {ψ {TQ X} (kerP {TQ X} (a w) (g w) (g-pr w) r) (∫ᶠ {X} f)} {Bf r}
          (mψ {TQ X} (kerP {TQ X} (a w) (g w) (g-pr w) r) (∫ᶠ {X} f)) (mBf r)
          (λ s → *-cong (proj₁ (Func.cong (map (a w)) (R≈.sym (merge-evens r s) , R≈.sym (merge-odds r s))))
                   (trans (proj₂ (Func.cong (map (a w)) (R≈.sym (merge-evens r s) , R≈.sym (merge-odds r s))) f)
                          (secEq {X} {νw} w₂ f (mergeR r s))))))

    eq′ : ∀ r → _≈ᴹ_ {X} (joinPre {X} (β r)) (kerP {X} a′ g′ gpr′ r)
    eq′ r f = trans (Sec.stepA f r) (sym (Sec.stepC f r))

  joinT : ∀ X → Hom S (TQ (TQ X)) (TQ X)
  joinT X = record
    { map = record
        { to = joinPre {X}
        ; cong = λ {p} {q} e f → trans (∫ᴹ-join p f) (trans (e (∫ᶠ f)) (sym (∫ᴹ-join q f))) }
    ; map-random = λ {β} w → record
        { a = JoinWit.a′ {X} {β ⟨$⟩_} w ; g = JoinWit.g′ {X} {β ⟨$⟩_} w ; g-ok = JoinWit.gok′ {X} {β ⟨$⟩_} w
        ; g-pr = JoinWit.gpr′ {X} {β ⟨$⟩_} w ; w-eq = JoinWit.eq′ {X} {β ⟨$⟩_} w }
    }

  -- the monad laws follow from the integral equations (`QBS.IntegralMonad`)
  integral : Integral S (QBS.Carrier WQ) (L.suc L.zero)
  integral = record
    { tests = record
        { Test = λ X → Hom S X WQ
        ; eval = λ f x → map f ⟨$⟩ x
        ; eval-cong = λ f e → Func.cong (map f) e
        ; _∘ᵗ_ = _∘H_ S
        ; eval-∘ = λ _ _ _ → refl
        }
    ; TQ = TQ
    ; ∫ = λ X p f → ∫ᴹ {X} p f
    ; ∫-ext = λ _ e → e
    ; ∫-cong = λ X p e → ∫ᴹ-cong {X} p e
    ; ∫ᶠ = λ X f → ∫ᶠ {X} f
    ; eval-∫ᶠ = λ _ _ _ → refl
    }

  monadData : MonadData integral
  monadData = record
    { TH = TH
    ; ηH = ηM
    ; joinH = joinT
    ; ∫-map = λ {X} {Y} f p g → ∫ᴹ-map {X} {Y} f p g
    ; ∫-η = λ X x f → ∫ᴹ-η {X} x f
    ; ∫-join = λ X p f → ∫ᴹ-join {X} p f
    }

  open Laws integral monadData public using (TF; ηN; μN; TM)

  TT : Endofunctor (QBSCat S)
  TT = TF ∘F TF
