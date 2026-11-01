{-# OPTIONS --safe --without-K #-}

-- Cantor space as a sample space: splitting into even and odd bits (the isomorphism
-- ℛ ≅ ℛ × ℛ in QBS), and the unit interval [0,1] as a QBS whose random elements are the
-- measurable functions.  No function extensionality, and no excluded middle.
module QBS.Continuous.Sample where

import Level as L
open import Level using (Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base using (ℕ; _+_; ⌊_/2⌋)
import Data.Nat.Base as ℕ
open import Data.Nat.Properties using (+-suc; n≡⌊n+n/2⌋)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q)
import QBS.Probes as Probes
open import QBS.Borel.Core
open import QBS.Borel.Source
open import QBS.Borel.Merge
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun

S = cantorSource
R = R₁

----------------------------------------------------------------------------
-- even and odd bits

dbl : ℕ → ℕ
dbl n = n + n

dbl-suc : ∀ n → dbl (ℕ.suc n) ≡ ℕ.suc (ℕ.suc (dbl n))
dbl-suc n = ≡.cong ℕ.suc (+-suc n n)

ev-dbl : ∀ n → ev (dbl n) ≡ true
ev-dbl ℕ.zero = ≡.refl
ev-dbl (ℕ.suc n) = ≡.trans (≡.cong ev (dbl-suc n)) (ev-dbl n)

ev-sdbl : ∀ n → ev (ℕ.suc (dbl n)) ≡ false
ev-sdbl ℕ.zero = ≡.refl
ev-sdbl (ℕ.suc n) = ≡.trans (≡.cong (λ m → ev (ℕ.suc m)) (dbl-suc n)) (ev-sdbl n)

half-sdbl : ∀ n → ⌊ ℕ.suc (dbl n) /2⌋ ≡ n
half-sdbl ℕ.zero = ≡.refl
half-sdbl (ℕ.suc n) = ≡.trans (≡.cong (λ m → ⌊ ℕ.suc m /2⌋) (dbl-suc n)) (≡.cong ℕ.suc (half-sdbl n))

-- every index is double its half, or one more
even-split : ∀ n → ev n ≡ true → n ≡ dbl ⌊ n /2⌋
even-split ℕ.zero _ = ≡.refl
even-split (ℕ.suc ℕ.zero) ()
even-split (ℕ.suc (ℕ.suc n)) e = ≡.trans (≡.cong (λ x → ℕ.suc (ℕ.suc x)) (even-split n e)) (≡.sym (dbl-suc ⌊ n /2⌋))

odd-split : ∀ n → ev n ≡ false → n ≡ ℕ.suc (dbl ⌊ n /2⌋)
odd-split ℕ.zero ()
odd-split (ℕ.suc ℕ.zero) _ = ≡.refl
odd-split (ℕ.suc (ℕ.suc n)) e = ≡.trans (≡.cong (λ x → ℕ.suc (ℕ.suc x)) (odd-split n e))
                                   (≡.cong ℕ.suc (≡.sym (dbl-suc ⌊ n /2⌋)))

evens odds : Cantor → Cantor
evens k n = k (dbl n)
odds k n = k (ℕ.suc (dbl n))

-- pointwise laws
merge-split : ∀ k n → mergeC (evens k) (odds k) n ≡ k n
merge-split k n with ev n in en
... | true = ≡.cong k (≡.sym (even-split n en))
... | false = ≡.cong k (≡.sym (odd-split n en))

evens-merge : ∀ a b n → evens (mergeC a b) n ≡ a n
evens-merge a b n = ≡.trans (≡.cong (λ e → if e then a h else b h) (ev-dbl n)) (≡.cong a (≡.sym (n≡⌊n+n/2⌋ n)))
  where h = ⌊ dbl n /2⌋

odds-merge : ∀ a b n → odds (mergeC a b) n ≡ b n
odds-merge a b n = ≡.trans (≡.cong (λ e → if e then a h else b h) (ev-sdbl n)) (≡.cong b (half-sdbl n))
  where h = ⌊ ℕ.suc (dbl n) /2⌋

merge-cong : ∀ {a a′ b b′} → ≡._≗_ a a′ → ≡._≗_ b b′ → ≡._≗_ (mergeC a b) (mergeC a′ b′)
merge-cong ea eb n = ≡.cong₂ (λ x y → if ev n then x else y) (ea ⌊ n /2⌋) (eb ⌊ n /2⌋)

----------------------------------------------------------------------------
-- at the level of the sample space R

mergeR : R → R → R
mergeR a b = lift (mergeC (lower a) (lower b))

evensR oddsR : R → R
evensR r = lift (evens (lower r))
oddsR r = lift (odds (lower r))

measurable-evens : Measurable evens
measurable-evens n b = gen (dbl n) b

measurable-odds : Measurable odds
measurable-odds n b = gen (ℕ.suc (dbl n)) b

measurable-merge : ∀ {a b : Cantor → Cantor} → Measurable a → Measurable b →
  Measurable (λ k → mergeC (a k) (b k))
measurable-merge {a} {b} ma mb n β with ev n
... | true = ma ⌊ n /2⌋ β
... | false = mb ⌊ n /2⌋ β

module R≈ = Setoid (RandomSource.Rˢ S)

evensR-cong : ∀ {r s} → r R≈.≈ s → evensR r R≈.≈ evensR s
evensR-cong e = lift (λ n → lower e (dbl n))

oddsR-cong : ∀ {r s} → r R≈.≈ s → oddsR r R≈.≈ oddsR s
oddsR-cong e = lift (λ n → lower e (ℕ.suc (dbl n)))

mergeR-cong : ∀ {a a′ b b′} → a R≈.≈ a′ → b R≈.≈ b′ → mergeR a b R≈.≈ mergeR a′ b′
mergeR-cong e₁ e₂ = lift (merge-cong (lower e₁) (lower e₂))

-- (r , s) ↦ (merge r (evens s) , odds s)
reassocR : Func (RandomSource.Rˢ S ×ₛ RandomSource.Rˢ S) (RandomSource.Rˢ S ×ₛ RandomSource.Rˢ S)
reassocR = record
  { to = λ p → mergeR (proj₁ p) (evensR (proj₂ p)) , oddsR (proj₂ p)
  ; cong = λ (e₁ , e₂) → mergeR-cong e₁ (evensR-cong e₂) , oddsR-cong e₂ }

-- the isomorphism ℛ ≅ ℛ × ℛ in QBS
fromH : Hom S (Probes.ℛQ S) (_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S))
fromH = record
  { map = record
      { to = λ r → evensR r , oddsR r
      ; cong = λ e → evensR-cong e , oddsR-cong e }
  ; map-random = λ {α} mα → measurable-∘ mα measurable-evens , measurable-∘ mα measurable-odds
  }

toH : Hom S (_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)) (Probes.ℛQ S)
toH = record
  { map = record
      { to = λ p → mergeR (proj₁ p) (proj₂ p)
      ; cong = λ (e₁ , e₂) → mergeR-cong e₁ e₂ }
  ; map-random = λ {α} (m₁ , m₂) → measurable-merge m₁ m₂
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
    ; probes = record
        { Random = λ h → Fun (λ r → proj₁ (h ⟨$⟩ r))
        ; random-resp = λ e f → Fun-ext e f
        ; const-random = λ x → Fun-const (proj₁ x) (proj₂ x)
        ; pre-random = λ f mf → Fun-pre f mf
        }
    ; glue-random = λ {i} pi hs fs → glueU {i ⟨$⟩_} pi (λ n r → proj₁ (hs n ⟨$⟩ r)) fs
    }
