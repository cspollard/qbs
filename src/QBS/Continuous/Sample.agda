{-# OPTIONS --safe --without-K #-}

-- Cantor space as a sample space: splitting into even and odd bits (the isomorphism
-- ℛ ≅ ℛ × ℛ in QBS), and the unit interval [0,1] as a QBS whose random elements are the
-- measurable functions.  Function extensionality is assumed only for the isomorphism laws.
module QBS.Continuous.Sample where

import Level as L
open import Level using (Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; _+_)
import Data.Nat.Base as ℕ
open import Data.Nat.Properties using (+-suc)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
open import Axiom.Extensionality.Propositional using (Extensionality)

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
ev-dbl (ℕ.suc n) rewrite +-suc n n = ev-dbl n

hf-dbl : ∀ n → hf (dbl n) ≡ n
hf-dbl ℕ.zero = ≡.refl
hf-dbl (ℕ.suc n) rewrite +-suc n n = ≡.cong ℕ.suc (hf-dbl n)

ev-sdbl : ∀ n → ev (ℕ.suc (dbl n)) ≡ false
ev-sdbl ℕ.zero = ≡.refl
ev-sdbl (ℕ.suc n) rewrite +-suc n n = ev-sdbl n

hf-sdbl : ∀ n → hf (ℕ.suc (dbl n)) ≡ n
hf-sdbl ℕ.zero = ≡.refl
hf-sdbl (ℕ.suc n) rewrite +-suc n n = ≡.cong ℕ.suc (hf-sdbl n)

-- every index is double its half, or one more
even-split : ∀ n → ev n ≡ true → n ≡ dbl (hf n)
even-split ℕ.zero _ = ≡.refl
even-split (ℕ.suc ℕ.zero) ()
even-split (ℕ.suc (ℕ.suc n)) e = ≡.trans (≡.cong (λ x → ℕ.suc (ℕ.suc x)) (even-split n e)) (≡.sym (dbl-suc (hf n)))

odd-split : ∀ n → ev n ≡ false → n ≡ ℕ.suc (dbl (hf n))
odd-split ℕ.zero ()
odd-split (ℕ.suc ℕ.zero) _ = ≡.refl
odd-split (ℕ.suc (ℕ.suc n)) e = ≡.trans (≡.cong (λ x → ℕ.suc (ℕ.suc x)) (odd-split n e))
                                   (≡.cong ℕ.suc (≡.sym (dbl-suc (hf n))))

evens odds : Cantor → Cantor
evens k n = k (dbl n)
odds k n = k (ℕ.suc (dbl n))

-- pointwise laws
merge-split : ∀ k n → mergeC (evens k) (odds k) n ≡ k n
merge-split k n with ev n in en
... | true = ≡.cong k (≡.sym (even-split n en))
... | false = ≡.cong k (≡.sym (odd-split n en))

evens-merge : ∀ a b n → evens (mergeC a b) n ≡ a n
evens-merge a b n rewrite ev-dbl n | hf-dbl n = ≡.refl

odds-merge : ∀ a b n → odds (mergeC a b) n ≡ b n
odds-merge a b n rewrite ev-sdbl n | hf-sdbl n = ≡.refl

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
... | true = ma (hf n) β
... | false = mb (hf n) β

-- the isomorphism ℛ ≅ ℛ × ℛ in QBS
fromH : Hom S (Probes.ℛQ S) (_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S))
fromH = record
  { map = record
      { to = λ r → evensR r , oddsR r
      ; cong = λ { ≡.refl → ≡.refl , ≡.refl } }
  ; map-random = λ {α} mα → measurable-∘ mα measurable-evens , measurable-∘ mα measurable-odds
  }

toH : Hom S (_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)) (Probes.ℛQ S)
toH = record
  { map = record
      { to = λ p → mergeR (proj₁ p) (proj₂ p)
      ; cong = λ { (≡.refl , ≡.refl) → ≡.refl } }
  ; map-random = λ {α} (m₁ , m₂) → measurable-merge m₁ m₂
  }

module Split (funext : Extensionality L.zero L.zero) where
  split-merge : ∀ r → mergeR (evensR r) (oddsR r) ≡ r
  split-merge r = ≡.cong lift (funext (merge-split (lower r)))

  merge-evens : ∀ r s → evensR (mergeR r s) ≡ r
  merge-evens r s = ≡.cong lift (funext (evens-merge (lower r) (lower s)))

  merge-odds : ∀ r s → oddsR (mergeR r s) ≡ s
  merge-odds r s = ≡.cong lift (funext (odds-merge (lower r) (lower s)))

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
    ; Random = λ h → Fun (λ r → proj₁ (h r))
    ; random-resp = λ e f → Fun-ext e f
    ; const-random = λ x → Fun-const (proj₁ x) (proj₂ x)
    ; pre-random = λ f mf → Fun-pre f mf
    ; glue-random = λ {i} pi hs fs → glueU pi (λ n r → proj₁ (hs n r)) fs
    }
