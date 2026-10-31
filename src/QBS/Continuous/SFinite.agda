{-# OPTIONS --safe --without-K #-}

-- The s-finite measure monad of the continuous model.  A measure on X is a pre-measure on W × X
-- (probe α : R → W × X, probability measure m on R): the weighted integral of a test function
-- f : X → W is J m (r ↦ w(α r) · f(x(α r))), and two measures are equal when all these agree
-- (so a weight is not distinguished from a mixture, as it must not be).  A random family of
-- measures has the same joint-probe witnesses as the probability monad of `Continuous/Monad`, with
-- the weaker equality; unbounded integrals are `J` of `Analysis/Lebesgue`, and `join` is Tonelli.
module QBS.Continuous.SFinite where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (R₁; cantorSource)
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

module SFinite (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zero⇒)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open UnitInterval A lem using (AQ)
  open RandomSource S using () renaming (meas-id to measId)
  module C = Continuous A lem probClass
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  -- measures on X are pre-measures on W × X
  XW : QBS S → QBS S
  XW X = _×Q_ S WQ X

  ----------------------------------------------------------------------------
  -- the weighted integral

  ψ : ∀ {X : QBS S} → Pre (XW X) → Hom S X WQ → R₁ → Cut
  ψ p f r = proj₁ (α p r) * (map f ⟨$⟩ proj₂ (α p r))

  abstract
    mψ : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) → Meas (ψ {X} p f)
    mψ {X} p f = Meas-⊗ {λ r → proj₁ (α p r)} {λ r → map f ⟨$⟩ proj₂ (α p r)}
      (proj₁ (α-random p)) (map-random f {λ r → proj₂ (α p r)} (proj₂ (α-random p)))

  ∫ᴹ : ∀ {X : QBS S} → Pre (XW X) → Hom S X WQ → Cut
  ∫ᴹ {X} p f = J (m p) (ψ {X} p f) (mψ {X} p f)

  _≈ᴹ_ : ∀ {X : QBS S} → Pre (XW X) → Pre (XW X) → Set₁
  _≈ᴹ_ {X} p q = ∀ f → ∫ᴹ {X} p f ≈ ∫ᴹ {X} q f

  PreMS : QBS S → Setoid (L.suc L.zero) (L.suc L.zero)
  PreMS X = record
    { Carrier = Pre (XW X)
    ; _≈_ = _≈ᴹ_ {X}
    ; isEquivalence = record
        { refl = λ _ → refl
        ; sym = λ e f → sym (e f)
        ; trans = λ e e′ f → trans (e f) (e′ f)
        }
    }

  -- the bounded truncation of a weighted test function is a bounded test function on W × X
  trH : ∀ {X : QBS S} → ℕ → Hom S X WQ → Hom S (XW X) AQ
  trH {X} k f = record
    { map = record
        { to = λ p → tr k (proj₁ p * (map f ⟨$⟩ proj₂ p)) , tr-≤1 k (proj₁ p * (map f ⟨$⟩ proj₂ p))
        ; cong = λ { (e₁ , e₂) → tr-cong k (*-cong e₁ (Func.cong (map f) e₂)) } }
    ; map-random = λ {γ} (m₁ , m₂) →
        FunInf-Meas {λ r → proj₁ (γ r) * (map f ⟨$⟩ proj₂ (γ r))}
          (Meas-⊗ {λ r → proj₁ (γ r)} {λ r → map f ⟨$⟩ proj₂ (γ r)} m₁ (map-random f {λ r → proj₂ (γ r)} m₂)) k
    }

  -- the truncation witnesses are opaque: they only ever appear as arguments of `I`
  abstract
    FIψ : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) → FunInf (ψ {X} p f)
    FIψ {X} p f = FunInf-Meas (mψ {X} p f)

  -- the integral of a truncation is the bounded integral of the truncated test function
  I-trH : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) k →
    I (m p) (λ x → tr k (ψ {X} p f x)) (FIψ {X} p f k) ≈ C.∫ {XW X} p (trH k f)
  I-trH {X} p f k = I-cong (m p) {λ x → tr k (ψ {X} p f x)} {λ r → proj₁ (map (trH k f) ⟨$⟩ α p r)}
    (λ r → refl) (FIψ {X} p f k) (map-random (trH k f) {α p} (α-random p))

  -- bounded equality implies weighted equality
  ≈ᵖ⇒≈ᴹ : ∀ {X : QBS S} (p q : Pre (XW X)) → C._≈ᵖ_ {XW X} p q → _≈ᴹ_ {X} p q
  ≈ᵖ⇒≈ᴹ {X} p q e f = J-trunc′ (m p) (m q) {ψ {X} p f} {ψ {X} q f} (mψ {X} p f) (mψ {X} q f)
    (FIψ {X} p f) (FIψ {X} q f)
    (λ k → trans (I-trH {X} p f k) (trans (e (trH k f)) (sym (I-trH {X} q f k))))

  ----------------------------------------------------------------------------
  -- random families of measures

  -- the pre-measure of the section of a joint probe at r
  kerP : ∀ {X : QBS S} (a : Joint (XW X)) (g : R₁ → Measure) → (∀ r → IsProb (g r)) → R₁ → Pre (XW X)
  kerP a g pr r = mk (sec a r) (sec-random a r) (g r) (pr r)

  record WitM {X : QBS S} (β : R₁ → Pre (XW X)) : Set₁ where
    field
      a : Joint (XW X)
      g : R₁ → Measure
      g-ok : KernelOk g
      g-pr : ∀ r → IsProb (g r)
      w-eq : ∀ r → _≈ᴹ_ {X} (β r) (kerP {X} a g g-pr r)

  open WitM

  fromWit : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → C.Wit {XW X} β → WitM {X} β
  fromWit {X} {β} w = record
    { a = C.Wit.a {XW X} {β} w ; g = C.Wit.g {XW X} {β} w ; g-ok = C.Wit.g-ok {XW X} {β} w
    ; g-pr = C.Wit.g-pr {XW X} {β} w
    ; w-eq = λ r → ≈ᵖ⇒≈ᴹ {X} (β r) (kerP {X} (C.Wit.a {XW X} {β} w) (C.Wit.g {XW X} {β} w) (C.Wit.g-pr {XW X} {β} w) r)
                    (C.Wit.w-eq {XW X} {β} w r) }

  -- The proofs of randomness are produced by `abstract` helpers: conversions at nested measure
  -- spaces (`TQ (X ×Q TQ Y)`, ...) must never unfold these witnesses (see TODO, compile time).
  abstract
    TQ-resp : ∀ {X : QBS S} {α β : R₁ → Pre (XW X)} → (∀ r → _≈ᴹ_ {X} (α r) (β r)) → WitM {X} α → WitM {X} β
    TQ-resp {X} e w = record
      { a = a w ; g = g w ; g-ok = g-ok w ; g-pr = g-pr w
      ; w-eq = λ r f → trans (sym (e r f)) (w-eq w r f) }

    TQ-const : ∀ {X : QBS S} (p : Pre (XW X)) → WitM {X} (const p)
    TQ-const {X} p = fromWit {X} (QBS.const-random (C.TQ (XW X)) p)

    TQ-pre : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} {f : R₁ → R₁} → WitM {X} β → RandomSource.Meas S f → WitM {X} (β ∘ f)
    TQ-pre {X} {β} {f} w mf = record
      { a = preJ mf (a w)
      ; g = λ r → g w (f r)
      ; g-ok = λ fh → Fun-pre (g-ok w fh) mf
      ; g-pr = λ r → g-pr w (f r)
      ; w-eq = λ r h → trans (w-eq w (f r) h)
          (≈ᵖ⇒≈ᴹ {X} (kerP {X} (a w) (g w) (g-pr w) (f r)) (kerP {X} (preJ mf (a w)) (λ r′ → g w (f r′)) (λ r′ → g-pr w (f r′)) r)
             (C.rand-irrel {XW X} (sec-random (a w) (f r)) (sec-random (preJ mf (a w)) r) (g w (f r)) (g-pr w (f r))) h) }

    TQ-glue : ∀ {X : QBS S} {i : R₁ → ℕ} → RandomSource.Idx S i → (β : ℕ → R₁ → Pre (XW X)) →
      (∀ n → WitM {X} (β n)) → WitM {X} (λ r → β (i r) r)
    TQ-glue {X} {i} pi β ws = record
      { a = glueJ pi (λ n → a (ws n))
      ; g = λ r → g (ws (i r)) r
      ; g-ok = λ {h} fh → Glue.Fun-glue i pi (λ n r → I (g (ws n) r) h fh) (λ n → g-ok (ws n) fh)
      ; g-pr = λ r → g-pr (ws (i r)) r
      ; w-eq = λ r h → trans (w-eq (ws (i r)) r h)
          (≈ᵖ⇒≈ᴹ {X} (kerP {X} (a (ws (i r))) (g (ws (i r))) (g-pr (ws (i r))) r)
             (kerP {X} (glueJ pi (λ n → a (ws n))) (λ r′ → g (ws (i r′)) r′) (λ r′ → g-pr (ws (i r′)) r′) r)
             (C.mk-cong {XW X} (sec-random (a (ws (i r))) r) (sec-random (glueJ pi (λ n → a (ws n))) r)
                (g (ws (i r)) r) (g-pr (ws (i r)) r) (λ s → Setoid.refl (Carrier (XW X)))) h) }

  -- the weighted test function of a joint probe at the merged parameter
  φJ : ∀ {X : QBS S} → Joint (XW X) → Hom S X WQ → R₁ → Cut
  φJ a f k = proj₁ (map a ⟨$⟩ (evensR k , oddsR k)) * (map f ⟨$⟩ proj₂ (map a ⟨$⟩ (evensR k , oddsR k)))

  -- a joint probe is random in the merged parameter
  paJ : ∀ {X : QBS S} (a : Joint (XW X)) → Random (XW X) (λ k → map a ⟨$⟩ (evensR k , oddsR k))
  paJ {X} a = map-random (_∘H_ S a fromH) {λ k → k} measId

  abstract
    mφJ : ∀ {X : QBS S} (a : Joint (XW X)) (f : Hom S X WQ) → Meas (φJ {X} a f)
    mφJ {X} a f = Meas-⊗ {λ k → proj₁ (map a ⟨$⟩ (evensR k , oddsR k))}
      {λ k → map f ⟨$⟩ proj₂ (map a ⟨$⟩ (evensR k , oddsR k))}
      (proj₁ (paJ {X} a)) (map-random f {λ k → proj₂ (map a ⟨$⟩ (evensR k , oddsR k))} (proj₂ (paJ {X} a)))

  -- the integral of a measure given by a section of a joint probe, as a parametric integral
  secEq : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} (w : WitM {X} β) (f : Hom S X WQ) (r : R₁) →
    ∫ᴹ {X} (β r) f ≈ J (g w r) (λ s → φJ {X} (a w) f (mergeR r s))
      (Meas-pre {φJ {X} (a w) f} {mergeR r} (mφJ {X} (a w) f) (measurable-merge₁ (lower r)))
  secEq {X} {β} w f r = trans (w-eq w r f)
    (J-cong (g w r) {ψ {X} (kerP {X} (a w) (g w) (g-pr w) r) f} {λ s → φJ {X} (a w) f (mergeR r s)}
      (mψ {X} (kerP {X} (a w) (g w) (g-pr w) r) f)
      (Meas-pre {φJ {X} (a w) f} {mergeR r} (mφJ {X} (a w) f) (measurable-merge₁ (lower r)))
      (λ s → *-cong (proj₁ (Func.cong (map (a w)) (R≈.sym (merge-evens r s) , R≈.sym (merge-odds r s))))
                    (Func.cong (map f) (proj₂ (Func.cong (map (a w)) (R≈.sym (merge-evens r s) , R≈.sym (merge-odds r s)))))))

  -- the integral against a random family of measures is measurable in the parameter
  ∫ᴹ-Meas : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} (w : WitM {X} β) (f : Hom S X WQ) → Meas (λ r → ∫ᴹ {X} (β r) f)
  ∫ᴹ-Meas {X} {β} w f = Meas-ext {λ r → J (g w r) (λ s → φJ {X} (a w) f (mergeR r s))
          (Meas-pre {φJ {X} (a w) f} {mergeR r} (mφJ {X} (a w) f) (measurable-merge₁ (lower r)))}
        {λ r → ∫ᴹ {X} (β r) f} (λ r → sym (secEq {X} {β} w f r))
        (Meas-Jsec (g w) (g-ok w) {φJ {X} (a w) f} (mφJ {X} (a w) f))

  TQ : QBS S → QBS S
  TQ X .QBS.Carrier = PreMS X
  TQ X .QBS.Random = WitM {X}
  TQ X .QBS.random-resp = TQ-resp {X}
  TQ X .QBS.random-cong {β} w e f = Meas-resp (∫ᴹ-Meas {X} {β} w f) (lower e)
  TQ X .QBS.const-random p = TQ-const {X} p
  TQ X .QBS.pre-random w mf = TQ-pre {X} w mf
  TQ X .QBS.glue-random pi β ws = TQ-glue {X} pi β ws

  ----------------------------------------------------------------------------
  -- functor action

  fW : ∀ {X Y : QBS S} → Hom S X Y → Hom S (XW X) (XW Y)
  fW {X} {Y} f = pairQ S {XW X} {WQ} {Y} (fstQ S {WQ} {X}) (_∘H_ S f (sndQ S {WQ} {X}))

  -- `mapM` and `joinPre` are opaque: later conversions never unfold their (large) probes and witnesses
  abstract
    mapM : ∀ {X Y : QBS S} → Hom S X Y → Pre (XW X) → Pre (XW Y)
    mapM {X} {Y} f = C.mapPre {XW X} {XW Y} (fW f)

    ∫ᴹ-map : ∀ {X Y : QBS S} (f : Hom S X Y) (p : Pre (XW X)) (h : Hom S Y WQ) →
      ∫ᴹ {Y} (mapM f p) h ≈ ∫ᴹ {X} p (_∘H_ S h f)
    ∫ᴹ-map {X} {Y} f p h = J-cong (m p) {ψ {Y} (mapM f p) h} {ψ {X} p (_∘H_ S h f)}
      (mψ {Y} (mapM f p) h) (mψ {X} p (_∘H_ S h f)) (λ r → refl)

  TH : ∀ {X Y : QBS S} → Hom S X Y → Hom S (TQ X) (TQ Y)
  TH {X} {Y} f = record
    { map = record
        { to = mapM f
        ; cong = λ {p} {q} e h → trans (∫ᴹ-map f p h) (trans (e (_∘H_ S h f)) (sym (∫ᴹ-map f q h))) }
    ; map-random = λ {β} w → record
        { a = _∘H_ S (fW f) (a w) ; g = g w ; g-ok = g-ok w ; g-pr = g-pr w
        ; w-eq = λ r h → trans (∫ᴹ-map f (β r) h)
            (trans (w-eq w r (_∘H_ S h f))
              (J-cong (g w r)
                {ψ {X} (kerP {X} (a w) (g w) (g-pr w) r) (_∘H_ S h f)}
                {ψ {Y} (kerP {Y} (_∘H_ S (fW f) (a w)) (g w) (g-pr w) r) h}
                (mψ {X} (kerP {X} (a w) (g w) (g-pr w) r) (_∘H_ S h f))
                (mψ {Y} (kerP {Y} (_∘H_ S (fW f) (a w)) (g w) (g-pr w) r) h) (λ s → refl))) }
    }

  ∫ᴹ-cong : ∀ {X : QBS S} (p : Pre (XW X)) {f h : Hom S X WQ} →
    (∀ x → map f ⟨$⟩ x ≈ map h ⟨$⟩ x) → ∫ᴹ {X} p f ≈ ∫ᴹ {X} p h
  ∫ᴹ-cong {X} p {f} {h} e = J-cong (m p) {ψ {X} p f} {ψ {X} p h} (mψ {X} p f) (mψ {X} p h)
    (λ r → *-cong refl (e (proj₂ (α p r))))

  ----------------------------------------------------------------------------
  -- unit

  ηM : ∀ X → Hom S X (TQ X)
  ηM X = record
    { map = record
        { to = λ x → C.ηPre {XW X} (1# , x)
        ; cong = λ {x} {y} e → ≈ᵖ⇒≈ᴹ {X} (C.ηPre {XW X} (1# , x)) (C.ηPre {XW X} (1# , y))
            (Func.cong (map (C.ηH (XW X))) {1# , x} {1# , y} (refl , e)) }
    ; map-random = λ {γ} rγ → fromWit {X} (map-random (C.ηH (XW X)) {λ r → 1# , γ r} (Meas-const 1# , rγ))
    }

  ∫ᴹ-η : ∀ {X : QBS S} (x : ∣ X ∣) (f : Hom S X WQ) → ∫ᴹ {X} (C.ηPre {XW X} (1# , x)) f ≈ map f ⟨$⟩ x
  ∫ᴹ-η {X} x f = trans (J-dirac r₀ {ψ {X} (C.ηPre {XW X} (1# , x)) f} (mψ {X} (C.ηPre {XW X} (1# , x)) f))
    (*-identityˡ _)

  ----------------------------------------------------------------------------
  -- integration as a test function on measures

  ∫ᶠ : ∀ {X : QBS S} → Hom S X WQ → Hom S (TQ X) WQ
  ∫ᶠ {X} f = record
    { map = record { to = λ p → ∫ᴹ {X} p f ; cong = λ e → e f }
    ; map-random = λ {β} w → ∫ᴹ-Meas {X} {β} w f
    }

  ----------------------------------------------------------------------------
  -- join

  -- the weight and test function of a doubly weighted joint probe
  wmOf : ∀ {X : QBS S} (p : Pre (XW (TQ X))) → WitM {X} (λ r → proj₂ (α p r))
  wmOf p = proj₂ (α-random p)

  abstract
    Ψ₂ : ∀ {X : QBS S} (p : Pre (XW (TQ X))) (WM : WitM {X} (λ r → proj₂ (α p r))) → R₁ → R₁ → ∣ XW X ∣
    Ψ₂ {X} p WM r s = proj₁ (α p r) * proj₁ (map (a WM) ⟨$⟩ (r , s)) , proj₂ (map (a WM) ⟨$⟩ (r , s))

    joinPre : ∀ {X : QBS S} → Pre (XW (TQ X)) → Pre (XW X)
    joinPre {X} p = mk (λ k → Ψ₂ {X} p (wmOf {X} p) (evensR k) (oddsR k))
      ( Meas-⊗ {λ k → proj₁ (α p (evensR k))} {λ k → proj₁ (map (a (wmOf {X} p)) ⟨$⟩ (evensR k , oddsR k))}
          (Meas-pre {λ r → proj₁ (α p r)} {evensR} (proj₁ (α-random p)) measurable-evens)
          (proj₁ (paJ {X} (a (wmOf {X} p))))
      , proj₂ (paJ {X} (a (wmOf {X} p))))
      (bind (m p) (P₁.pushMerge (g (wmOf {X} p))) (P₁.KernelOk-pushMerge {g (wmOf {X} p)} (g-ok (wmOf {X} p))))
      (IsProb-bind {m p} {P₁.pushMerge (g (wmOf {X} p))} {P₁.KernelOk-pushMerge {g (wmOf {X} p)} (g-ok (wmOf {X} p))} (ok p)
         (λ r → IsProb-push {mergeR r} (measurable-merge₁ (lower r)) {g (wmOf {X} p) r} (g-pr (wmOf {X} p) r)))

    -- the r-th section kernel of the witness of `p`, as a pre-measure on X
    joinKer : ∀ {X : QBS S} (p : Pre (XW (TQ X))) → R₁ → Pre (XW X)
    joinKer {X} p r = kerP {X} (a (wmOf {X} p)) (g (wmOf {X} p)) (g-pr (wmOf {X} p)) r

    -- Tonelli: the integral of a join is the integral of the integrals
    ∫ᴹ-join-pt : ∀ {X : QBS S} (p : Pre (XW (TQ X))) (f : Hom S X WQ) (r s : R₁) → ψ {X} (joinPre {X} p) f (mergeR r s)
                 ≈ proj₁ (α p r) * ψ {X} (joinKer {X} p r) f s
    ∫ᴹ-join-pt {X} p f r s = trans
      (*-cong (*-cong (proj₁ (random-cong (XW (TQ X)) (α-random p) (merge-evens r s)))
                      (proj₁ (Func.cong (map (a (wmOf {X} p))) (merge-evens r s , merge-odds r s))))
              (Func.cong (map f) (proj₂ (Func.cong (map (a (wmOf {X} p))) (merge-evens r s , merge-odds r s)))))
      (*-assoc _ _ _)


    ∫ᴹ-join-inner : ∀ {X : QBS S} (p : Pre (XW (TQ X))) (f : Hom S X WQ) (r : R₁) →
      J (P₁.pushMerge (g (wmOf {X} p)) r) (ψ {X} (joinPre {X} p) f) (mψ {X} (joinPre {X} p) f)
        ≈ ψ {TQ X} p (∫ᶠ {X} f) r
    ∫ᴹ-join-inner {X} p f r = trans
      (J-push {mergeR r} (measurable-merge₁ (lower r)) (g (wmOf {X} p) r) {ψ {X} (joinPre {X} p) f}
         (mψ {X} (joinPre {X} p) f)
         (Meas-pre {ψ {X} (joinPre {X} p) f} {mergeR r} (mψ {X} (joinPre {X} p) f) (measurable-merge₁ (lower r))))
      (trans
        (J-cong (g (wmOf {X} p) r) {λ s → ψ {X} (joinPre {X} p) f (mergeR r s)}
           {λ s → proj₁ (α p r) * ψ {X} (joinKer {X} p r) f s}
           (Meas-pre {ψ {X} (joinPre {X} p) f} {mergeR r} (mψ {X} (joinPre {X} p) f) (measurable-merge₁ (lower r)))
           (Meas-⊗ {λ _ → proj₁ (α p r)} {ψ {X} (joinKer {X} p r) f}
              (Meas-const (proj₁ (α p r))) (mψ {X} (joinKer {X} p r) f))
           (λ s → ∫ᴹ-join-pt {X} p f r s))
        (trans (J-scale (g (wmOf {X} p) r) (proj₁ (α p r)) {ψ {X} (joinKer {X} p r) f}
                  (mψ {X} (joinKer {X} p r) f))
          (*-cong refl (sym (w-eq (wmOf {X} p) r f)))))

    ∫ᴹ-join : ∀ {X : QBS S} (p : Pre (XW (TQ X))) (f : Hom S X WQ) →
      ∫ᴹ {X} (joinPre {X} p) f ≈ ∫ᴹ {TQ X} p (∫ᶠ {X} f)
    ∫ᴹ-join {X} p f = trans
      (J-bind (m p) (P₁.pushMerge (g (wmOf {X} p))) (P₁.KernelOk-pushMerge {g (wmOf {X} p)} (g-ok (wmOf {X} p)))
          {ψ {X} (joinPre {X} p) f}
        (mψ {X} (joinPre {X} p) f)
        (Meas-J (P₁.pushMerge (g (wmOf {X} p))) (P₁.KernelOk-pushMerge {g (wmOf {X} p)} (g-ok (wmOf {X} p)))
            {ψ {X} (joinPre {X} p) f}
          (mψ {X} (joinPre {X} p) f)))
      (J-cong (m p) {λ r → J (P₁.pushMerge (g (wmOf {X} p)) r) (ψ {X} (joinPre {X} p) f) (mψ {X} (joinPre {X} p) f)}
        {ψ {TQ X} p (∫ᶠ {X} f)}
        (Meas-J (P₁.pushMerge (g (wmOf {X} p))) (P₁.KernelOk-pushMerge {g (wmOf {X} p)} (g-ok (wmOf {X} p)))
            {ψ {X} (joinPre {X} p) f}
          (mψ {X} (joinPre {X} p) f))
        (mψ {TQ X} p (∫ᶠ {X} f))
        (∫ᴹ-join-inner {X} p f))
