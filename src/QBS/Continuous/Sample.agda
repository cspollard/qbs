{-# OPTIONS --safe --without-K #-}

-- Cantor space as a sample space: splitting into even and odd bits (the isomorphism
-- ℛ ≅ ℛ × ℛ in QBS), and the unit interval [0,1] as a QBS whose random elements are the
-- measurable functions.  No function extensionality, and no excluded middle.
module QBS.Continuous.Sample where

import Level as L
open import Level using (lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; _+_)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product.Function.NonDependent.Setoid using (<_,_>ₛ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; rand-fst; rand-snd; rand-pair)
open import QBS.Pieces
import Categories.Category.SubCategory.SubHom as SH
open import Categories.Category.Instance.Setoids using (Setoids)
import QBS.Probes as Probes
open import QBS.Borel.Core
open import QBS.Borel.Source
open import QBS.Borel.Merge
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun

S = cantorSource
R = R₁

open RandomSource S using (Meas; meas₀; meas-∘; measurable)
open SH (Setoids (L.suc L.zero) (L.suc L.zero)) using (mem; probe; reads)

-- Partial application of a morphism on a product: `fixL x f = y ↦ f (x , y)` and `fixR y f = x ↦ f (x , y)`, into any
-- value space V (the test functions `AQ`/`WQ` of the probability and s-finite strengths are the two uses).
fixL : ∀ {X Y V : QBS S} → QBS.∣ X ∣ → Hom S (_×Q_ S X Y) V → Hom S Y V
fixL {X} {Y} x f = record
  { map = record
      { to = λ y → Hom.map f ⟨$⟩ (x , y)
      ; cong = λ e → Func.cong (Hom.map f) (Setoid.refl (QBS.Carrier X) , e) }
  ; map-random = λ {γ} rγ → Hom.map-random f {< constₛ x , γ >ₛ} (rand-pair S {X} {Y} {< constₛ x , γ >ₛ} (QBS.const-random X x) rγ)
  }

fixR : ∀ {X Y V : QBS S} → QBS.∣ Y ∣ → Hom S (_×Q_ S X Y) V → Hom S X V
fixR {X} {Y} y f = record
  { map = record
      { to = λ x → Hom.map f ⟨$⟩ (x , y)
      ; cong = λ e → Func.cong (Hom.map f) (e , Setoid.refl (QBS.Carrier Y)) }
  ; map-random = λ {γ} rγ → Hom.map-random f {< γ , constₛ y >ₛ} (rand-pair S {X} {Y} {< γ , constₛ y >ₛ} rγ (QBS.const-random Y y))
  }

----------------------------------------------------------------------------
-- even and odd bits

evens odds : Cantor → Cantor
evens k n = k (n + n)
odds k n = k (ℕ.suc (n + n))

-- pointwise laws
merge-split : ∀ k n → mergeC (evens k) (odds k) n ≡ k n
merge-split k n with even-or-odd n
... | j , inj₁ ≡.refl = mergeC-even j (evens k) (odds k)
... | j , inj₂ ≡.refl = mergeC-odd j (evens k) (odds k)

evens-merge : ∀ a b n → evens (mergeC a b) n ≡ a n
evens-merge a b n = mergeC-even n a b

odds-merge : ∀ a b n → odds (mergeC a b) n ≡ b n
odds-merge a b n = mergeC-odd n a b

merge-cong : ∀ {a a′ b b′} → ≡._≗_ a a′ → ≡._≗_ b b′ → ≡._≗_ (mergeC a b) (mergeC a′ b′)
merge-cong ea eb zero = ea zero
merge-cong ea eb (ℕ.suc n) = merge-cong eb (λ k → ea (ℕ.suc k)) n

----------------------------------------------------------------------------
-- at the level of the sample space R

mergeR : R → R → R
mergeR a b = lift (mergeC (lower a) (lower b))

evensR oddsR : R → R
evensR r = lift (evens (lower r))
oddsR r = lift (odds (lower r))

measurable-evens : Measurable evens
measurable-evens n b = gen (n + n) b

measurable-odds : Measurable odds
measurable-odds n b = gen (ℕ.suc (n + n)) b

module R≈ = Setoid (RandomSource.Rˢ S)

evensR-cong : ∀ {r s} → r R≈.≈ s → evensR r R≈.≈ evensR s
evensR-cong e = lift (λ n → lower e (n + n))

oddsR-cong : ∀ {r s} → r R≈.≈ s → oddsR r R≈.≈ oddsR s
oddsR-cong e = lift (λ n → lower e (ℕ.suc (n + n)))

mergeR-cong : ∀ {a a′ b b′} → a R≈.≈ a′ → b R≈.≈ b′ → mergeR a b R≈.≈ mergeR a′ b′
mergeR-cong e₁ e₂ = lift (merge-cong (lower e₁) (lower e₂))

-- (r , s) ↦ (merge r (evens s) , odds s)
reassocR : Func (RandomSource.Rˢ S ×ₛ RandomSource.Rˢ S) (RandomSource.Rˢ S ×ₛ RandomSource.Rˢ S)
reassocR = record
  { to = λ p → mergeR (proj₁ p) (evensR (proj₂ p)) , oddsR (proj₂ p)
  ; cong = λ (e₁ , e₂) → mergeR-cong e₁ (evensR-cong e₂) , oddsR-cong e₂ }

-- the raw measurability of the map read by a random element of ℛ
raw : ∀ {f} → Meas f → Measurable (down (f ⟨$⟩_))
raw m = measurable-ext (λ x → lower (reads m {lift x})) (proj₂ (probe m))

-- an index map that is random is a Borel partition
idxPart : ∀ {i} → RandomSource.Idx S i → Partition (downℕ (λ r → lower (i ⟨$⟩ r)))
idxPart {i} pi = part-resp {a = proj₁ (probe pi)} {b = i} (λ r → reads pi {r}) (proj₂ (probe pi))

evensₛ oddsₛ : Func (RandomSource.Rˢ S) (RandomSource.Rˢ S)
evensₛ = record { to = evensR ; cong = evensR-cong }
oddsₛ = record { to = oddsR ; cong = oddsR-cong }

-- the isomorphism ℛ ≅ ℛ × ℛ in QBS
fromH : Hom S (Probes.ℛQ S) (_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S))
fromH = record
  { map = record
      { to = λ r → evensR r , oddsR r
      ; cong = λ e → evensR-cong e , oddsR-cong e }
  ; map-random = λ {α} mα →
      rand-pair S {Probes.ℛQ S} {Probes.ℛQ S} {< evensₛ , oddsₛ >ₛ ∘ₛ α}
        (meas-∘ (meas₀ {evensₛ} measurable-evens) mα) (meas-∘ (meas₀ {oddsₛ} measurable-odds) mα)
  }

toH : Hom S (_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)) (Probes.ℛQ S)
toH = record
  { map = record
      { to = λ p → mergeR (proj₁ p) (proj₂ p)
      ; cong = λ (e₁ , e₂) → mergeR-cong e₁ e₂ }
  ; map-random = λ {α} m →
      meas₀ (measurable-merge (raw (rand-fst S {Probes.ℛQ S} {Probes.ℛQ S} {α} m))
                              (raw (rand-snd S {Probes.ℛQ S} {Probes.ℛQ S} {α} m)))
  }

-- the round trips, up to `≈ᴿ` (pointwise equality of sequences): no function extensionality
split-merge : ∀ r → Setoid._≈_ (RandomSource.Rˢ S) (mergeR (evensR r) (oddsR r)) r
split-merge r = lift (merge-split (lower r))

merge-evens : ∀ r s → Setoid._≈_ (RandomSource.Rˢ S) (evensR (mergeR r s)) r
merge-evens r s = lift (evens-merge (lower r) (lower s))

merge-odds : ∀ r s → Setoid._≈_ (RandomSource.Rˢ S) (oddsR (mergeR r s)) s
merge-odds r s = lift (odds-merge (lower r) (lower s))

----------------------------------------------------------------------------
-- the unit interval: random elements are the measurable functions

module UnitInterval (A : OmegaSemiring (L.suc L.zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A

  𝕀 : Setoid (L.suc L.zero) (L.suc L.zero)
  𝕀 = record
    { Carrier = Σ ∣A∣ (λ a → a ≤ 1#)
    ; _≈_ = λ a b → proj₁ a ≈ proj₁ b
    ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
    }

  private
    glueU : ∀ {i : R → ℕ} (pi : Partition (downℕ i)) (hs : ℕ → R → ∣A∣) →
      (∀ n → Fun (hs n)) → Fun (λ x → hs (i x) x)
    glueU {i} pi hs fs = Glue.Fun-glue i pi hs fs

  AQ : QBS S
  AQ = record
    { Carrier = 𝕀
    ; probes = fromPred measurable 𝕀 (λ h → Fun (λ r → proj₁ (h ⟨$⟩ r)))
        (λ x → Fun-const (proj₁ x) (proj₂ x)) (λ f mf → Fun-pre f mf)
    ; glue-random = λ {i} pi hs fs →
        let q = λ n → probe (fs n)
            β = λ n → proj₁ (q n) in
        mem (glueₛ i β , glueU {λ r → lower (i ⟨$⟩ r)} (idxPart pi) (λ n r → proj₁ (β n ⟨$⟩ r)) (λ n → proj₂ (q n)))
          (λ {r} → reads (fs (lower (i ⟨$⟩ r))) {r})
    }

  -- random elements of AQ are the measurable functions (up to the pointwise equality in the reading)
  rand-Fun : ∀ {h : Func (RandomSource.Rˢ S) 𝕀} → QBS.Random AQ h → Fun (λ r → proj₁ (h ⟨$⟩ r))
  rand-Fun m = Fun-ext (λ r → reads m {r}) (proj₂ (probe m))

  Fun-rand : ∀ {h : Func (RandomSource.Rˢ S) 𝕀} → Fun (λ r → proj₁ (h ⟨$⟩ r)) → QBS.Random AQ h
  Fun-rand {h} f = mem (h , f) refl
