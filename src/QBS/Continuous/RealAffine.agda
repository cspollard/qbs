{-# OPTIONS --safe --without-K #-}

-- Addition and signed scaling on the real line `RQ = WQ +Q WQ` as morphisms, and affine maps RQⁿ ⇒ RQᵐ, each a QBS morphism.
--   * `copair×ˡ f g : (X +Q Y) ×Q Z ⇒ W` from `f : X ×Q Z ⇒ W` and `g : Y ×Q Z ⇒ W` (distributivity of × over +, in the
--     form needed for maps out of a product), `copair×ʳ` for the second factor; the computations `copair×ˡ-inl`/`-inr`;
--   * `addW`, `monusP : WQ ×Q WQ ⇒ WQ`, (a, b) ↦ a + b and a ∸ b, and the pair of Borel facts they need on random elements
--     (`Meas-monus`, `le₂-borel`); `mixH : WQ ×Q WQ ⇒ RQ`, (a, b) ↦ a − b (`inl (a ∸ b)` if b ≤ a, else `inr (b ∸ a)`, the
--     glued map of `RealShift.shiftRH` with a varying shift), with `mix-le`, `mix-gt`;
--   * `addRH : RQ ×Q RQ ⇒ RQ`, (x, y) ↦ x + y, from the four sign combinations (`add-ll`, `add-rr`, `add-lr-le`, `add-lr-gt`,
--     `add-rl-le`, `add-rl-gt`); `zeroRQ`, `constRQ c`, the constant `c = c⁺ − c⁻ : Sg`; `scaleSRH c : RQ ⇒ RQ`, x ↦ c x for a
--     signed constant c (`scaleRH c⁺` and `reflRH ∘ scaleRH c⁻`, added);
--   * n-ary sums and linear forms: `sumRH n : RQⁿ ⇒ RQ`, `linRH n a : RQⁿ ⇒ RQ`, x ↦ Σᵢ aᵢ xᵢ, and the affine map
--     `affRH M b : RQⁿ ⇒ RQᵐ` as the `tupleQ` of the rows `rowRH`, x ↦ A x + b;
--   * the laws against the signed test `idT` (x⁺ − x⁻), as signed tests `_≐_` (cross-multiplied, `SignedTest`):
--     `idT-add`, `idT-scaleS`, `idT-constRQ`, `idT-sumRH`, `idT-linRH`, `idT-rowRH`, and for a map Z into RQⁿ
--     `idT-affRH`: the coordinates of A Z + b computed in RQᵐ agree with `RandomVector.affT` on the coordinates of Z.
-- Route: `RQ ×Q RQ ⇒ RQ` is not obtainable from the constant-shift `RealShift.shiftRH` (joint measurability is the point), so
-- `copair×ˡ` reduces it to four maps WQ ×Q WQ ⇒ RQ: `inl ∘ addW`, `inr ∘ addW` and `mixH` (twice, once swapped).  `copair×ˡ`:
-- a random pair (α, β) has α glued on a partition j (`QBS.Random` of `+Q`); on each piece `pre-random`/`pair` gives a random
-- pair into X ×Q Z, push it through f or g, and glue with `glue-random` of W.  `addW = FatouAux.addX fst snd` (`Meas-⊕`).
-- `Meas-monus`: mem (a ∸ b) q is ∃ p, b ≤ p ∧ a > p + q, a countable union of Borel sets (`Meas.pair-enum`, `LipTestAlg.le-borel`
-- style); `le₂-borel` is `le-borel` with the variable bound (same `all-enum` argument).  `mixRand` follows `RealShift.gRand`
-- (flag `flg`, partition `flg-part`, pieces a ∸ b and b ∸ a from `monusP` and its swap).  The `idT` laws are case splits on the
-- signs: `monus-add` (bounded subtrahend), `monus-zero`, `mix-le`, `mix-gt`, `add-*`; `idT-sumRH` by induction on n using
-- `idT-add`, `idT-linRH` from `idT-scaleS`, `idT-affRH` from the rows, `proj-tuple` and `SgMoments.sumT`.  Since `≐` is not
-- transitive at infinite points, the n-ary laws go through the stronger invariant `RealAffineAlg.Inv` (cross equality, and
-- bounded targets give bounded parts), which composes through sums (`InvP-add`, `sumInv`, `lin-gen`, `row-gen`).
module QBS.Continuous.RealAffine where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (lift)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Colimits using (_+Q_; Piece; ev)
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ)
open import QBS.Borel.Core using (Pred; Partition; Borel; resp; union₂; inter₂)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.LowerReals using (Cut; module Cut; _⊑_)
open import Data.Rational.Unnormalised.Base using (_<_) renaming (_+_ to _+q_)
open import QBS.Analysis.RationalLemmas using (ℚᵘ; 0ℚᵘ)
open import QBS.Borel.Source using (idxₛ)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open Cut using (mem)
open _⊑_ using (ap)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealScale using (module RealScale)
open import QBS.Continuous.RealShift using (module RealShift)
open import QBS.Continuous.Monus using (module Monus)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.RandomVector using (module RandomVector)
open import QBS.Continuous.RealAffineAlg using (module RealAffineAlg)

module RealAffine (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; +-comm; commutativeSemiring)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Sg; Bnd; _≃_)
  open Sg
  open SgLinAlg (Bounded.signedRing A) using (Vec; Mat)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (module C)
  open FatouAux lem₁ using (addX; imp-borel)
  open RealLine lem₁ using (RQ; inlH; inrH)
  open RealScale lem₁ using (scaleRH; reflRH)
  open RealShift lem₁ using (_≈ᴿ_; inl≈; inr≈; dec; pick; pick-le; pick-gt; flg; flg-part; pieces-ev)
  open Intervals (lemOf lem₁) using (Ge)
  open Monus lem₁ using (monus; monus-cong; BndQ)
  open LevelSets (lemOf lem₁) using (borel-prop)
  open ProdMap (lemOf lem₁) using (swapQ)
  open RandomSource S using (Rˢ)
  open Meas (lemOf lem₁) using (Meas; ex-enum; all-enum)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _≐_; _+T_; _∘T_; scaleT; constT; idT)
  open SgMoments lem₁ using (sumT)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; proj-tuple)
  open RealAffineAlg lem₁ using (Inv; Inv-of; step-inv; monus-add*; not-le; z+; +z)
  open RandomVector lem₁ using (affT)
  open QBS
  open Hom

  -- real vectors RQⁿ
  RQⁿ : ℕ → QBS S
  RQⁿ n = ΠQ n (λ _ → RQ)

  ----------------------------------------------------------------------------
  -- maps out of a product with a coproduct factor

  -- the pairing of two setoid maps out of Rˢ
  prₛ : ∀ {A B : QBS S} → Func Rˢ (Carrier A) → Func Rˢ (Carrier B) → Func Rˢ (Carrier (_×Q_ S A B))
  prₛ a b = record { to = λ r → a ⟨$⟩ r , b ⟨$⟩ r ; cong = λ e → Func.cong a e , Func.cong b e }

  module _ {X Y Z W : QBS S} (f : Hom S (_×Q_ S X Z) W) (g : Hom S (_×Q_ S Y Z) W) where

    copair×ᶠ : Func (Carrier (_×Q_ S (_+Q_ S X Y) Z)) (Carrier W)
    copair×ᶠ = record
      { to = λ { (inj₁ x , z) → map f ⟨$⟩ (x , z) ; (inj₂ y , z) → map g ⟨$⟩ (y , z) }
      ; cong = λ { {inj₁ _ , _} {inj₁ _ , _} (⊎ʳ.inj₁ e , ez) → Func.cong (map f) (e , ez)
                 ; {inj₂ _ , _} {inj₂ _ , _} (⊎ʳ.inj₂ e , ez) → Func.cong (map g) (e , ez) } }

    -- the pair (piece, β) pushed through f or g
    pieceFn : Func Rˢ (Carrier Z) → Piece S X Y → Func Rˢ (Carrier W)
    pieceFn β (inj₁ (a , _)) = map f ∘ₛ prₛ {X} {Z} a β
    pieceFn β (inj₂ (b , _)) = map g ∘ₛ prₛ {Y} {Z} b β

    pieceRand : ∀ {β} → Random Z β → ∀ cn → Random W (pieceFn β cn)
    pieceRand {β} pβ (inj₁ (a , pa)) = map-random f {prₛ {X} {Z} a β}
      (random-resp X (λ _ → Setoid.refl (Carrier X)) pa , random-resp Z (λ _ → Setoid.refl (Carrier Z)) pβ)
    pieceRand {β} pβ (inj₂ (b , pb)) = map-random g {prₛ {Y} {Z} b β}
      (random-resp Y (λ _ → Setoid.refl (Carrier Y)) pb , random-resp Z (λ _ → Setoid.refl (Carrier Z)) pβ)

    pieceEq : ∀ cn β r (w : ∣ _×Q_ S (_+Q_ S X Y) Z ∣) → Setoid._≈_ (Carrier (_+Q_ S X Y)) (proj₁ w) (ev S X Y cn r) →
      Setoid._≈_ (Carrier Z) (proj₂ w) (β ⟨$⟩ r) → Setoid._≈_ (Carrier W) (copair×ᶠ ⟨$⟩ w) (pieceFn β cn ⟨$⟩ r)
    pieceEq (inj₁ _) β r (inj₁ _ , _) (⊎ʳ.inj₁ ex) ez = Func.cong (map f) (ex , ez)
    pieceEq (inj₂ _) β r (inj₂ _ , _) (⊎ʳ.inj₂ ey) ez = Func.cong (map g) (ey , ez)

    c×rand : ∀ {α} → Random (_+Q_ S X Y) (proj₁ₛ ∘ₛ α) → Random Z (proj₂ₛ ∘ₛ α) → Random W (copair×ᶠ ∘ₛ α)
    c×rand {α} (i , ii , c , q) pB = random-resp W {glueₛ i (λ n → pieceFn (proj₂ₛ ∘ₛ α) (c n))} {copair×ᶠ ∘ₛ α}
      (λ r → Setoid.sym (Carrier W) (pieceEq (c (i ⟨$⟩ r)) (proj₂ₛ ∘ₛ α) r (α ⟨$⟩ r) (q r) (Setoid.refl (Carrier Z))))
      (glue-random W ii (λ n → pieceFn (proj₂ₛ ∘ₛ α) (c n)) (λ n → pieceRand pB (c n)))

    -- a random pair is glued on the partition of its first coordinate; each piece is random in X ×Q Z or Y ×Q Z
    copair×ˡ : Hom S (_×Q_ S (_+Q_ S X Y) Z) W
    copair×ˡ = record { map = copair×ᶠ ; map-random = λ {α} (pA , pB) → c×rand {α} pA pB }

  copair×ˡ-inl : ∀ {X Y Z W : QBS S} (f : Hom S (_×Q_ S X Z) W) (g : Hom S (_×Q_ S Y Z) W) x z →
    Setoid._≈_ (Carrier W) (map (copair×ˡ f g) ⟨$⟩ (inj₁ x , z)) (map f ⟨$⟩ (x , z))
  copair×ˡ-inl {W = W} f g x z = Setoid.refl (Carrier W)

  copair×ˡ-inr : ∀ {X Y Z W : QBS S} (f : Hom S (_×Q_ S X Z) W) (g : Hom S (_×Q_ S Y Z) W) y z →
    Setoid._≈_ (Carrier W) (map (copair×ˡ f g) ⟨$⟩ (inj₂ y , z)) (map g ⟨$⟩ (y , z))
  copair×ˡ-inr {W = W} f g y z = Setoid.refl (Carrier W)

  -- the same for the second factor, by swapping
  copair×ʳ : ∀ {X Y Z W : QBS S} → Hom S (_×Q_ S Z X) W → Hom S (_×Q_ S Z Y) W → Hom S (_×Q_ S Z (_+Q_ S X Y)) W
  copair×ʳ f g = _∘H_ S (copair×ˡ (_∘H_ S f swapQ) (_∘H_ S g swapQ)) swapQ

  ----------------------------------------------------------------------------
  -- addition and truncated subtraction on the half-line WQ

  addW : Hom S (_×Q_ S WQ WQ) WQ
  addW = addX {_×Q_ S WQ WQ} (fstQ S) (sndQ S)

  -- measurability of a ∸ b, and of the set {b ≤ a}, along a random pair
  Meas-monus : ∀ {α β : Func Rˢ (Carrier WQ)} → Meas (α ⟨$⟩_) → Meas (β ⟨$⟩_) → Meas (λ r → monus (α ⟨$⟩ r) (β ⟨$⟩ r))
  Meas-monus {α} {β} mα mβ q = resp (λ c → (λ x → x) , (λ x → x)) (union₂ (borel-prop (q < 0ℚᵘ)) (inter₂ bB (ex-enum P bP)))
    where
      bB : Borel (λ c → BndQ (β ⟨$⟩ lift c))
      bB = ex-enum (λ M c → ∀ s → mem (β ⟨$⟩ lift c) s → s < M)
        (λ M → all-enum (λ s c → mem (β ⟨$⟩ lift c) s → s < M) (λ s → imp-borel (mβ s) (borel-prop (s < M))))
      P : ℚᵘ → Pred
      P q′ c = (q < q′) × (∀ s → mem (β ⟨$⟩ lift c) s → mem (α ⟨$⟩ lift c) (q′ +q s))
      bP : ∀ q′ → Borel (P q′)
      bP q′ = inter₂ (borel-prop (q < q′)) (all-enum (λ s c → mem (β ⟨$⟩ lift c) s → mem (α ⟨$⟩ lift c) (q′ +q s))
        (λ s → imp-borel (mβ s) (mα (q′ +q s))))

  monusP : Hom S (_×Q_ S WQ WQ) WQ
  monusP = record
    { map = record { to = λ p → monus (proj₁ p) (proj₂ p) ; cong = λ { (e₁ , e₂) → monus-cong e₁ e₂ } }
    ; map-random = λ {γ} (m₁ , m₂) → Meas-monus {map (fstQ S {WQ} {WQ}) ∘ₛ γ} {map (sndQ S {WQ} {WQ}) ∘ₛ γ} m₁ m₂ }

  le₂-borel : ∀ {α β : Func Rˢ (Carrier WQ)} → Meas (α ⟨$⟩_) → Meas (β ⟨$⟩_) →
    Borel (λ c → Ge (β ⟨$⟩ lift c) (α ⟨$⟩ lift c))
  le₂-borel {α} {β} mα mβ = all-enum (λ ρ c → mem (β ⟨$⟩ lift c) ρ → mem (α ⟨$⟩ lift c) ρ)
    (λ ρ → imp-borel (mβ ρ) (mα ρ))

  ----------------------------------------------------------------------------
  -- (a, b) ↦ a − b on WQ ×Q WQ, glued as in `RealShift.gRand` with a varying shift

  Ge-cong : ∀ {t t′ x x′} → t ≈ t′ → x ≈ x′ → Ge x t → Ge x′ t′
  Ge-cong (tt , _) (_ , xx) g q m = ap tt q (g q (ap xx q m))

  pick-cong₂ : ∀ {t t′ x x′} → t ≈ t′ → x ≈ x′ → ∀ d e → pick t x d ≈ᴿ pick t′ x′ e
  pick-cong₂ et ex (inj₁ _) (inj₁ _) = inl≈ (monus-cong et ex)
  pick-cong₂ et ex (inj₁ a) (inj₂ n) = ⊥-elim (n (Ge-cong et ex a))
  pick-cong₂ et ex (inj₂ n) (inj₁ a) = ⊥-elim (n (Ge-cong (sym et) (sym ex) a))
  pick-cong₂ et ex (inj₂ _) (inj₂ _) = inr≈ (monus-cong ex et)

  mixF : Func (Carrier (_×Q_ S WQ WQ)) (Carrier RQ)
  mixF = record
    { to = λ p → pick (proj₁ p) (proj₂ p) (dec (proj₁ p) (proj₂ p))
    ; cong = λ { (e₁ , e₂) → pick-cong₂ e₁ e₂ _ _ } }

  -- the pieces a ∸ b on {b ≤ a} and b ∸ a on its complement
  mixPieces : ∀ {γ : Func Rˢ (Carrier (_×Q_ S WQ WQ))} → Random (_×Q_ S WQ WQ) γ → ℕ → Piece S WQ WQ
  mixPieces {γ} p zero = inj₁ (map monusP ∘ₛ γ , map-random monusP {γ} p)
  mixPieces {γ} p (suc _) = inj₂ (map (_∘H_ S monusP swapQ) ∘ₛ γ , map-random (_∘H_ S monusP swapQ) {γ} p)

  mixPieces-ev : ∀ {γ : Func Rˢ (Carrier (_×Q_ S WQ WQ))} (p : Random (_×Q_ S WQ WQ) γ) r d →
    pick (proj₁ (γ ⟨$⟩ r)) (proj₂ (γ ⟨$⟩ r)) d ≈ᴿ ev S WQ WQ (mixPieces {γ} p (flg d)) r
  mixPieces-ev p r (inj₁ _) = inl≈ refl
  mixPieces-ev p r (inj₂ _) = inr≈ refl

  mixRand : ∀ {γ : Func Rˢ (Carrier (_×Q_ S WQ WQ))} → Random (_×Q_ S WQ WQ) γ → Random RQ (mixF ∘ₛ γ)
  mixRand {γ} (m₁ , m₂) = idxₛ (λ r → flg (d r)) pt , pt , mixPieces {γ} (m₁ , m₂) , λ r → mixPieces-ev {γ} (m₁ , m₂) r (d r)
    where
      d = λ r → dec (proj₁ (γ ⟨$⟩ r)) (proj₂ (γ ⟨$⟩ r))
      pt = flg-part (le₂-borel {map (fstQ S {WQ} {WQ}) ∘ₛ γ} {map (sndQ S {WQ} {WQ}) ∘ₛ γ} m₁ m₂) (λ c → d (lift c))

  mixH : Hom S (_×Q_ S WQ WQ) RQ
  mixH = record { map = mixF ; map-random = λ {γ} p → mixRand {γ} p }

  mix-le : ∀ a b → b ≤ a → map mixH ⟨$⟩ (a , b) ≈ᴿ inj₁ (monus a b)
  mix-le a b ba = pick-le a b ba (dec a b)

  mix-gt : ∀ a b → (b ≤ a → ⊥) → map mixH ⟨$⟩ (a , b) ≈ᴿ inj₂ (monus b a)
  mix-gt a b nba = pick-gt a b nba (dec a b)

  ----------------------------------------------------------------------------
  -- addition RQ ×Q RQ ⇒ RQ: four sign combinations

  addRH : Hom S (_×Q_ S RQ RQ) RQ
  addRH = copair×ˡ (copair×ʳ (_∘H_ S inlH addW) mixH) (copair×ʳ (_∘H_ S mixH swapQ) (_∘H_ S inrH addW))

  add-ll : ∀ a b → map addRH ⟨$⟩ (inj₁ a , inj₁ b) ≈ᴿ inj₁ (a + b)
  add-ll a b = inl≈ refl

  add-rr : ∀ a b → map addRH ⟨$⟩ (inj₂ a , inj₂ b) ≈ᴿ inj₂ (a + b)
  add-rr a b = inr≈ refl

  add-lr-le : ∀ a b → b ≤ a → map addRH ⟨$⟩ (inj₁ a , inj₂ b) ≈ᴿ inj₁ (monus a b)
  add-lr-le a b ba = mix-le a b ba

  add-lr-gt : ∀ a b → (b ≤ a → ⊥) → map addRH ⟨$⟩ (inj₁ a , inj₂ b) ≈ᴿ inj₂ (monus b a)
  add-lr-gt a b nba = mix-gt a b nba

  add-rl-le : ∀ a b → a ≤ b → map addRH ⟨$⟩ (inj₂ a , inj₁ b) ≈ᴿ inj₁ (monus b a)
  add-rl-le a b ab = mix-le b a ab

  add-rl-gt : ∀ a b → (a ≤ b → ⊥) → map addRH ⟨$⟩ (inj₂ a , inj₁ b) ≈ᴿ inj₂ (monus a b)
  add-rl-gt a b nab = mix-gt b a nab

  ----------------------------------------------------------------------------
  -- constants, signed scaling, sums, linear forms, affine maps

  zeroRQ : ∀ {X : QBS S} → Hom S X RQ
  zeroRQ {X} = _∘H_ S inlH (constW {X} 0#)

  -- the constant c = c⁺ − c⁻
  constRQ : ∀ {X : QBS S} → Sg → Hom S X RQ
  constRQ {X} c = _∘H_ S addRH (pairQ S (_∘H_ S inlH (constW {X} (pos c))) (_∘H_ S inrH (constW {X} (neg c))))

  -- x ↦ c x = c⁺ x − c⁻ x
  scaleSRH : Sg → Hom S RQ RQ
  scaleSRH c = _∘H_ S addRH (pairQ S (scaleRH (pos c)) (_∘H_ S reflRH (scaleRH (neg c))))

  sumRH : ∀ n → Hom S (RQⁿ n) RQ
  sumRH zero = zeroRQ
  sumRH (suc n) = _∘H_ S addRH (pairQ S (fstQ S) (_∘H_ S (sumRH n) (sndQ S)))

  -- x ↦ Σᵢ aᵢ xᵢ
  linRH : ∀ n → (Fin n → Sg) → Hom S (RQⁿ n) RQ
  linRH n a = _∘H_ S (sumRH n) (tupleQ n (λ _ → RQ) (λ i → _∘H_ S (scaleSRH (a i)) (projQ n (λ _ → RQ) i)))

  -- the k-th row of x ↦ A x + b
  rowRH : ∀ {m n} → Mat m n → Vec m → Fin m → Hom S (RQⁿ n) RQ
  rowRH M b k = _∘H_ S addRH (pairQ S (linRH _ (M k)) (constRQ (b k)))

  affRH : ∀ {m n} → Mat m n → Vec m → Hom S (RQⁿ n) (RQⁿ m)
  affRH {m} M b = tupleQ m (λ _ → RQ) (rowRH M b)

  ----------------------------------------------------------------------------
  -- the laws against idT (x⁺ − x⁻)

  -- the parts of idT at a point of RQ
  idP : ∀ {u a} → u ≈ᴿ inj₁ a → (at⁺ idT u ≈ a) × (at⁻ idT u ≈ 0#)
  idP {inj₁ _} (⊎ʳ.inj₁ e) = e , refl

  idN : ∀ {u a} → u ≈ᴿ inj₂ a → (at⁺ idT u ≈ 0#) × (at⁻ idT u ≈ a)
  idN {inj₂ _} (⊎ʳ.inj₂ e) = refl , e

  zero-id : ∀ u → at⁺ idT u ≈ 0# ⊎ at⁻ idT u ≈ 0#
  zero-id (inj₁ _) = inj₂ refl
  zero-id (inj₂ _) = inj₁ refl

  cong-id : ∀ {u u′} → u ≈ᴿ u′ → (at⁺ idT u ≈ at⁺ idT u′) × (at⁻ idT u ≈ at⁻ idT u′)
  cong-id e = Func.cong (map (proj₁ idT)) e , Func.cong (map (proj₂ idT)) e

  cong4 : ∀ {p p′ q q′ r r′ s s′} → p ≈ p′ → q ≈ q′ → r ≈ r′ → s ≈ s′ → p′ + q′ ≈ r′ + s′ → p + q ≈ r + s
  cong4 a b c d e = trans (+-cong a b) (trans e (sym (+-cong c d)))

  -- a mixed-sign sum p − n: idT of the result against (p, n)
  core : ∀ p n (u : ∣ RQ ∣) → (n ≤ p → u ≈ᴿ inj₁ (monus p n)) → ((n ≤ p → ⊥) → u ≈ᴿ inj₂ (monus n p)) →
    at⁺ idT u + n ≈ p + at⁻ idT u
  core p n u l g with lem₁ (n ≤ p)
  ... | inj₁ h = cong4 (proj₁ (idP (l h))) refl refl (proj₂ (idP (l h)))
    (trans (+-comm _ _) (trans (monus-add* n p h) (sym (z+ p))))
  ... | inj₂ nh = cong4 (proj₁ (idN (g nh))) refl refl (proj₂ (idN (g nh)))
    (trans (+z n) (sym (monus-add* p n (not-le nh))))

  idT-lr : ∀ p n → at⁺ idT (map addRH ⟨$⟩ (inj₁ p , inj₂ n)) + n ≈ p + at⁻ idT (map addRH ⟨$⟩ (inj₁ p , inj₂ n))
  idT-lr p n = core p n _ (add-lr-le p n) (add-lr-gt p n)

  idT-rl : ∀ a b → at⁺ idT (map addRH ⟨$⟩ (inj₂ a , inj₁ b)) + a ≈ b + at⁻ idT (map addRH ⟨$⟩ (inj₂ a , inj₁ b))
  idT-rl a b = core b a _ (add-rl-le a b) (add-rl-gt a b)

  idT-add : _≐_ {_×Q_ S RQ RQ} (idT ∘T addRH) (_+T_ {_×Q_ S RQ RQ} (idT ∘T fstQ S) (idT ∘T sndQ S))
  idT-add (inj₁ a , inj₁ b) = cong4 (proj₁ (idP (add-ll a b))) refl refl (proj₂ (idP (add-ll a b)))
    (+-cong refl (+z 0#))
  idT-add (inj₂ a , inj₂ b) = cong4 (proj₁ (idN (add-rr a b))) refl refl (proj₂ (idN (add-rr a b)))
    (+-cong (sym (+z 0#)) refl)
  idT-add (inj₁ a , inj₂ b) = trans (+-cong refl (+z b)) (trans (idT-lr a b) (+-cong (sym (z+ a)) refl))
  idT-add (inj₂ a , inj₁ b) = trans (+-cong refl (z+ a)) (trans (idT-rl a b) (+-cong (sym (+z b)) refl))

  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring using (solve; con; _:*_; _:=_)

  m0 : ∀ x → x * 0# ≈ 0#
  m0 x = solve 1 (λ x → x :* con 0 := con 0) refl x

  mz⁺ : ∀ c a → pos c * a + neg c * 0# ≈ pos c * a
  mz⁺ c a = trans (+-cong refl (m0 _)) (z+ _)

  mz⁻ : ∀ c a → pos c * 0# + neg c * a ≈ neg c * a
  mz⁻ c a = trans (+-cong (m0 _) refl) (+z _)

  idT-scaleS : ∀ c → _≐_ {RQ} (idT ∘T scaleSRH c) (scaleT c idT)
  idT-scaleS c (inj₁ a) = trans (+-cong refl (mz⁻ c a)) (trans (idT-lr (pos c * a) (neg c * a)) (+-cong (sym (mz⁺ c a)) refl))
  idT-scaleS c (inj₂ a) = trans (+-cong refl (mz⁺ c a)) (trans (idT-rl (pos c * a) (neg c * a)) (+-cong (sym (mz⁻ c a)) refl))

  idT-constRQ : ∀ {X : QBS S} c → _≐_ {X} (idT ∘T constRQ {X} c) (constT c)
  idT-constRQ c x = idT-lr (pos c) (neg c)

  ----------------------------------------------------------------------------
  -- the invariant at a point, through sums

  InvP : ∣ RQ ∣ → ∣A∣ → ∣A∣ → Set₁
  InvP u P N = Inv (at⁺ idT u) (at⁻ idT u) P N

  InvP-of : ∀ u P N → at⁺ idT u + N ≈ P + at⁻ idT u → InvP u P N
  InvP-of u P N e = Inv-of (zero-id u) e

  InvP-resp : ∀ {u u′ P N} → u ≈ᴿ u′ → InvP u′ P N → InvP u P N
  InvP-resp {u} {u′} {P} {N} e (c , _) = InvP-of u P N
    (trans (+-cong (proj₁ (cong-id e)) refl) (trans c (+-cong refl (sym (proj₂ (cong-id e))))))

  InvP-add : ∀ v u {a b P N} → InvP v a b → InvP u P N → InvP (map addRH ⟨$⟩ (v , u)) (a + P) (b + N)
  InvP-add v u iv iu = step-inv (zero-id v) (zero-id u) (zero-id (map addRH ⟨$⟩ (v , u))) iv iu (idT-add (v , u))

  sumInv : ∀ {Ω : QBS S} n (Y : Hom S Ω (RQⁿ n)) (F : Fin n → SgT Ω) →
    (∀ i ω → InvP (map (projQ n (λ _ → RQ) i) ⟨$⟩ (map Y ⟨$⟩ ω)) (at⁺ (F i) ω) (at⁻ (F i) ω)) →
    ∀ ω → InvP (map (sumRH n) ⟨$⟩ (map Y ⟨$⟩ ω)) (at⁺ (sumT n F) ω) (at⁻ (sumT n F) ω)
  sumInv zero Y F h ω = InvP-of _ _ _ refl
  sumInv (suc n) Y F h ω = InvP-add _ _ (h fzero ω)
    (sumInv n (_∘H_ S (sndQ S) Y) (λ i → F (fsuc i)) (λ i → h (fsuc i)) ω)

  idT-sumRH : ∀ n → _≐_ {RQⁿ n} (idT ∘T sumRH n) (sumT n (λ i → idT ∘T projQ n (λ _ → RQ) i))
  idT-sumRH n x = proj₁ (sumInv n (idH S {RQⁿ n}) (λ i → idT ∘T projQ n (λ _ → RQ) i) (λ i ω → InvP-of _ _ _ refl) x)

  lin-gen : ∀ {Ω : QBS S} n (a : Fin n → Sg) (Z : Hom S Ω (RQⁿ n)) (G : Fin n → SgT Ω) →
    (∀ i ω → (at⁺ (G i) ω ≈ at⁺ (scaleT (a i) idT) (map (projQ n (λ _ → RQ) i) ⟨$⟩ (map Z ⟨$⟩ ω))) ×
             (at⁻ (G i) ω ≈ at⁻ (scaleT (a i) idT) (map (projQ n (λ _ → RQ) i) ⟨$⟩ (map Z ⟨$⟩ ω)))) →
    ∀ ω → InvP (map (linRH n a) ⟨$⟩ (map Z ⟨$⟩ ω)) (at⁺ (sumT n G) ω) (at⁻ (sumT n G) ω)
  lin-gen n a Z G hy = sumInv n (_∘H_ S (tupleQ n (λ _ → RQ) (λ i → _∘H_ S (scaleSRH (a i)) (projQ n (λ _ → RQ) i))) Z) G
    (λ i ω → InvP-resp (proj-tuple n (λ _ → RQ) (λ j → _∘H_ S (scaleSRH (a j)) (projQ n (λ _ → RQ) j)) i (map Z ⟨$⟩ ω))
      (InvP-of _ _ _ (trans (+-cong refl (proj₂ (hy i ω))) (trans (idT-scaleS (a i) _) (+-cong (sym (proj₁ (hy i ω))) refl)))))

  idT-linRH : ∀ n a → _≐_ {RQⁿ n} (idT ∘T linRH n a) (sumT n (λ i → scaleT (a i) (idT ∘T projQ n (λ _ → RQ) i)))
  idT-linRH n a x = proj₁ (lin-gen n a (idH S {RQⁿ n}) (λ i → scaleT (a i) (idT ∘T projQ n (λ _ → RQ) i))
    (λ i ω → refl , refl) x)

  row-gen : ∀ {Ω : QBS S} {m n} (M : Mat m n) b k (Z : Hom S Ω (RQⁿ n)) (G : Fin n → SgT Ω) →
    (∀ i ω → (at⁺ (G i) ω ≈ at⁺ (scaleT (M k i) idT) (map (projQ n (λ _ → RQ) i) ⟨$⟩ (map Z ⟨$⟩ ω))) ×
             (at⁻ (G i) ω ≈ at⁻ (scaleT (M k i) idT) (map (projQ n (λ _ → RQ) i) ⟨$⟩ (map Z ⟨$⟩ ω)))) →
    ∀ ω → InvP (map (rowRH M b k) ⟨$⟩ (map Z ⟨$⟩ ω)) (at⁺ (_+T_ {Ω} (sumT n G) (constT (b k))) ω)
      (at⁻ (_+T_ {Ω} (sumT n G) (constT (b k))) ω)
  row-gen M b k Z G hy ω = InvP-add _ _ (lin-gen _ (M k) Z G hy ω) (InvP-of _ _ _ (idT-constRQ (b k) (map Z ⟨$⟩ ω)))

  idT-rowRH : ∀ {m n} (M : Mat m n) b k → _≐_ {RQⁿ n} (idT ∘T rowRH M b k)
    (_+T_ {RQⁿ n} (sumT n (λ i → scaleT (M k i) (idT ∘T projQ n (λ _ → RQ) i))) (constT (b k)))
  idT-rowRH M b k x = proj₁ (row-gen M b k (idH S {RQⁿ _}) (λ i → scaleT (M k i) (idT ∘T projQ _ (λ _ → RQ) i))
    (λ i ω → refl , refl) x)

  -- the coordinates of A Z + b computed in RQᵐ are `RandomVector.affT` of the coordinates idT ∘ Zᵢ
  idT-affRH : ∀ {Ω : QBS S} (P : C.Pre Ω) {m n} (M : Mat m n) b (Z : Hom S Ω (RQⁿ n)) k →
    _≐_ {Ω} ((idT ∘T projQ m (λ _ → RQ) k) ∘T _∘H_ S (affRH M b) Z)
      (affT P M b (λ i → (idT ∘T projQ n (λ _ → RQ) i) ∘T Z) k)
  idT-affRH P {m} M b Z k ω = proj₁ (InvP-resp (proj-tuple m (λ _ → RQ) (rowRH M b) k (map Z ⟨$⟩ ω))
    (row-gen M b k Z (λ i → scaleT (M k i) ((idT ∘T projQ _ (λ _ → RQ) i) ∘T Z)) (λ i ω′ → refl , refl) ω))
