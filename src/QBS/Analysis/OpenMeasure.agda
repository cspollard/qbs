{-# OPTIONS --safe --without-K #-}

-- Open subsets of Cantor space as increasing chains of clopen sets, their measure ν (the
-- supremum of the clopen measures), and the consequences of compactness: ν depends only on the
-- set, ν is modular, and covers of the space by two opens have total measure ≥ 1.
module QBS.Analysis.OpenMeasure where

import Level as L
open import Data.Bool.Base using (Bool; true; false; not; _∨_; _∧_)
open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _<_)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core using (Cantor; Pred)
open import QBS.Analysis.Omega
open import QBS.Analysis.Series
open import QBS.Analysis.Archimedean
open import QBS.Analysis.Clopen
open import QBS.Analysis.ClopenMeasure

----------------------------------------------------------------------------
-- Boolean helpers

or-elim : ∀ a b → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
or-elim true b e = inj₁ ≡.refl
or-elim false b e = inj₂ e

or-inl : ∀ {a} b → a ≡ true → a ∨ b ≡ true
or-inl b ≡.refl = ≡.refl

or-inr : ∀ a {b} → b ≡ true → a ∨ b ≡ true
or-inr true ≡.refl = ≡.refl
or-inr false ≡.refl = ≡.refl

and-elim : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
and-elim true true e = ≡.refl , ≡.refl

and-intro : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
and-intro ≡.refl ≡.refl = ≡.refl

not-true : ∀ a → not a ≡ true → a ≡ false
not-true true ()
not-true false e = ≡.refl

not-false : ∀ a → a ≡ false → not a ≡ true
not-false .false ≡.refl = ≡.refl

module Opens {A : OmegaSemiring (L.suc L.zero)} (R : Arch A) (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R
  open Premeasure R
  open Series A
  open Fan lem
  open ArchLemmas R
  open SetoidReasoning setoid

  record Op : Set where
    field
      T : ℕ → Cl
      inc : ∀ N x → eval (T N) x ≡ true → eval (T (suc N)) x ≡ true
  open Op

  _∈ᵒ_ : Cantor → Op → Set
  x ∈ᵒ O = Σ ℕ (λ n → eval (T O n) x ≡ true)

  T-mono : ∀ O {N M} → N ℕ.≤′ M → ∀ x → eval (T O N) x ≡ true → eval (T O M) x ≡ true
  T-mono O ℕ.≤′-refl x e = e
  T-mono O {N} {suc M} (ℕ.≤′-step le) x e = inc O M x (T-mono O le x e)

  T-mono≤ : ∀ O {N M} → N ℕ.≤ M → ∀ x → eval (T O N) x ≡ true → eval (T O M) x ≡ true
  T-mono≤ O le = T-mono O (ℕₚ.≤⇒≤′ le)

  ν-inc : ∀ O → Increasing (λ n → μ0 (T O n))
  ν-inc O n = μ0-mono (T O n) (T O (suc n)) (inc O n)

  ν : Op → ∣A∣
  ν O = ⨆ (λ n → μ0 (T O n)) (ν-inc O)

  ν-ub : ∀ O n → μ0 (T O n) ≤ ν O
  ν-ub O = ⨆-ub (λ n → μ0 (T O n)) (ν-inc O)

  ν-≤1 : ∀ O → ν O ≤ 1#
  ν-≤1 O = ⨆-lub (λ n → μ0 (T O n)) (ν-inc O) (λ n → μ0-≤1 (T O n))

  ----------------------------------------------------------------------------
  -- compactness

  E-seq : Cl → Op → ℕ → Cl
  E-seq C O N = C ∩ ∁ᶜ (T O N)

  eval-E : ∀ C O N x → eval (E-seq C O N) x ≡ eval C x ∧ not (eval (T O N) x)
  eval-E C O N x = ≡.trans (eval-∩ C (∁ᶜ (T O N)) x) (≡.cong (eval C x ∧_) (eval-∁ (T O N) x))

  not-false-inv : ∀ a → not a ≡ false → a ≡ true
  not-false-inv true e = ≡.refl
  not-false-inv false ()

  E-dec : ∀ C O → Decreasing (E-seq C O)
  E-dec C O N x e with and-elim _ _ (≡.trans (≡.sym (eval-E C O (suc N) x)) e)
  ... | cx , nt = ≡.trans (eval-E C O N x) (and-intro cx (not-false _ (no-N (not-true _ nt))))
    where
      no-N : eval (T O (suc N)) x ≡ false → eval (T O N) x ≡ false
      no-N f with eval (T O N) x in q
      ... | false = ≡.refl
      ... | true = ≡.trans (≡.sym (inc O N x q)) f

  E-cover : ∀ C O → (∀ x → eval C x ≡ true → x ∈ᵒ O) → ∀ x → Σ ℕ (λ N → eval (E-seq C O N) x ≡ false)
  E-cover C O sub x with eval C x in cx
  ... | false = 0 , ≡.trans (eval-E C O 0 x) (≡.trans (≡.cong (_∧ _) cx) ≡.refl)
  ... | true with sub x cx
  ...   | n , en = n , ≡.trans (eval-E C O n x) (≡.trans (≡.cong (_∧ not (eval (T O n) x)) cx) (≡.cong not en))

  compact : ∀ C O → (∀ x → eval C x ≡ true → x ∈ᵒ O) →
    Σ ℕ (λ N → ∀ x → eval C x ≡ true → eval (T O N) x ≡ true)
  compact C O sub with fan (E-seq C O) (E-dec C O) (E-cover C O sub)
  ... | N , empty = N , λ x cx → not-false-inv _
    (≡.trans (≡.sym (≡.cong (_∧ not (eval (T O N) x)) cx)) (≡.trans (≡.sym (eval-E C O N x)) (empty x)))

  ν-mono : ∀ O P → (∀ x → x ∈ᵒ O → x ∈ᵒ P) → ν O ≤ ν P
  ν-mono O P sub = ⨆-lub (λ n → μ0 (T O n)) (ν-inc O) go
    where
      go : ∀ n → μ0 (T O n) ≤ ν P
      go n with compact (T O n) P (λ x e → sub x (n , e))
      ... | M , h = ≤-trans (μ0-mono (T O n) (T P M) h) (ν-ub P M)

  ν-cong : ∀ O P → (∀ x → x ∈ᵒ O → x ∈ᵒ P) → (∀ x → x ∈ᵒ P → x ∈ᵒ O) → ν O ≈ ν P
  ν-cong O P f g = ≤-antisym (ν-mono O P f) (ν-mono P O g)

  clopen : Cl → Op
  clopen C = record { T = λ _ → C ; inc = λ _ _ e → e }

  ν-clopen : ∀ C → ν (clopen C) ≈ μ0 C
  ν-clopen C = ⨆-const (μ0 C) (ν-inc (clopen C))

  ∪-mono : ∀ a b a′ b′ → (∀ x → eval a x ≡ true → eval a′ x ≡ true) → (∀ x → eval b x ≡ true → eval b′ x ≡ true) →
    ∀ x → eval (a ∪ b) x ≡ true → eval (a′ ∪ b′) x ≡ true
  ∪-mono a b a′ b′ ha hb x e = ≡.trans (eval-∪ a′ b′ x)
    (go (or-elim _ _ (≡.trans (≡.sym (eval-∪ a b x)) e)))
    where
      go : eval a x ≡ true ⊎ eval b x ≡ true → eval a′ x ∨ eval b′ x ≡ true
      go (inj₁ p) = or-inl _ (ha x p)
      go (inj₂ q) = or-inr _ (hb x q)

  ∩-mono : ∀ a b a′ b′ → (∀ x → eval a x ≡ true → eval a′ x ≡ true) → (∀ x → eval b x ≡ true → eval b′ x ≡ true) →
    ∀ x → eval (a ∩ b) x ≡ true → eval (a′ ∩ b′) x ≡ true
  ∩-mono a b a′ b′ ha hb x e with and-elim _ _ (≡.trans (≡.sym (eval-∩ a b x)) e)
  ... | p , q = ≡.trans (eval-∩ a′ b′ x) (and-intro (ha x p) (hb x q))

  infixl 6 _∪ᵒ_
  infixl 7 _∩ᵒ_
  _∪ᵒ_ _∩ᵒ_ : Op → Op → Op
  O ∪ᵒ P = record { T = λ N → T O N ∪ T P N
                  ; inc = λ N → ∪-mono (T O N) (T P N) (T O (suc N)) (T P (suc N)) (inc O N) (inc P N) }
  O ∩ᵒ P = record { T = λ N → T O N ∩ T P N
                  ; inc = λ N → ∩-mono (T O N) (T P N) (T O (suc N)) (T P (suc N)) (inc O N) (inc P N) }

  ∈-∪ᵒ← : ∀ {O P x} → x ∈ᵒ O ⊎ x ∈ᵒ P → x ∈ᵒ (O ∪ᵒ P)
  ∈-∪ᵒ← {O} {P} {x} (inj₁ (n , e)) = n , ≡.trans (eval-∪ (T O n) (T P n) x) (or-inl _ e)
  ∈-∪ᵒ← {O} {P} {x} (inj₂ (n , e)) = n , ≡.trans (eval-∪ (T O n) (T P n) x) (or-inr _ e)

  ∈-∩ᵒ← : ∀ {O P x} → x ∈ᵒ O → x ∈ᵒ P → x ∈ᵒ (O ∩ᵒ P)
  ∈-∩ᵒ← {O} {P} {x} (n , e) (m , f) = (n ⊔ m) , ≡.trans (eval-∩ (T O (n ⊔ m)) (T P (n ⊔ m)) x)
    (and-intro (T-mono≤ O (ℕₚ.m≤m⊔n n m) x e) (T-mono≤ P (ℕₚ.m≤n⊔m n m) x f))

  ν-mod : ∀ O P → ν (O ∪ᵒ P) + ν (O ∩ᵒ P) ≈ ν O + ν P
  ν-mod O P = begin
    ν (O ∪ᵒ P) + ν (O ∩ᵒ P)
      ≈⟨ ⨆-+-diag (ν-inc (O ∪ᵒ P)) (ν-inc (O ∩ᵒ P)) incS ⟩
    ⨆ (λ n → μ0 (T O n ∪ T P n) + μ0 (T O n ∩ T P n)) incS
      ≈⟨ ⨆-cong incS incS′ (λ n → μ0-mod (T O n) (T P n)) ⟩
    ⨆ (λ n → μ0 (T O n) + μ0 (T P n)) incS′
      ≈⟨ sym (⨆-+-diag (ν-inc O) (ν-inc P) incS′) ⟩
    ν O + ν P ∎
    where
      incS : Increasing (λ n → μ0 (T O n ∪ T P n) + μ0 (T O n ∩ T P n))
      incS n = +-mono (ν-inc (O ∪ᵒ P) n) (ν-inc (O ∩ᵒ P) n)
      incS′ : Increasing (λ n → μ0 (T O n) + μ0 (T P n))
      incS′ n = +-mono (ν-inc O n) (ν-inc P n)

  -- covering the space by two opens: the union has measure one
  ν-cover₁ : ∀ O P → (∀ x → x ∈ᵒ O ⊎ x ∈ᵒ P) → ν (O ∪ᵒ P) ≈ 1#
  ν-cover₁ O P cov with compact (leaf true) (O ∪ᵒ P) (λ x _ → ∈-∪ᵒ← {O} {P} (cov x))
  ... | N , h = ≤-antisym (ν-≤1 (O ∪ᵒ P))
    (≤-trans (μ0-mono (leaf true) (T O N ∪ T P N) h) (ν-ub (O ∪ᵒ P) N))

  ν-cover : ∀ O P → (∀ x → x ∈ᵒ O ⊎ x ∈ᵒ P) → 1# ≤ ν O + ν P
  ν-cover O P cov = ≤-trans (≤-reflexive (sym (ν-cover₁ O P cov)))
    (≤-trans ≤-+ʳ (≤-reflexive (ν-mod O P)))

  ----------------------------------------------------------------------------
  -- countable unions and finite intersections

  bigU : (ℕ → Cl) → ℕ → Cl
  bigU f zero = leaf false
  bigU f (suc i) = bigU f i ∪ f i

  bigU-in : ∀ f {i N} x → i < N → eval (f i) x ≡ true → eval (bigU f N) x ≡ true
  bigU-in f {i} {suc N} x lt e with ℕₚ.m≤n⇒m<n∨m≡n (ℕₚ.≤-pred lt)
  ... | inj₁ p = ≡.trans (eval-∪ (bigU f N) (f N) x) (or-inl _ (bigU-in f x p e))
  ... | inj₂ ≡.refl = ≡.trans (eval-∪ (bigU f i) (f i) x) (or-inr _ e)

  bigU-out : ∀ f N x → eval (bigU f N) x ≡ true → Σ ℕ (λ i → i < N × eval (f i) x ≡ true)
  bigU-out f zero x ()
  bigU-out f (suc N) x e with or-elim _ _ (≡.trans (≡.sym (eval-∪ (bigU f N) (f N) x)) e)
  ... | inj₁ p with bigU-out f N x p
  ...   | i , lt , q = i , ℕₚ.m<n⇒m<1+n lt , q
  bigU-out f (suc N) x e | inj₂ q = N , ℕₚ.n<1+n N , q

  bigU-μ0 : ∀ f N → μ0 (bigU f N) ≤ psum (λ i → μ0 (f i)) N
  bigU-μ0 f zero = ≤-refl
  bigU-μ0 f (suc N) = ≤-trans (μ0-∪≤ (bigU f N) (f N)) (+-mono (bigU-μ0 f N) ≤-refl)

  ⋃ᵒ : (ℕ → Op) → Op
  ⋃ᵒ O = record
    { T = λ N → bigU (λ i → T (O i) N) N
    ; inc = λ N x e → let i , lt , q = bigU-out (λ i → T (O i) N) N x e
                      in bigU-in (λ i → T (O i) (suc N)) x (ℕₚ.m<n⇒m<1+n lt) (inc (O i) N x q) }

  ν-⋃ᵒ : ∀ O → ν (⋃ᵒ O) ≤ ∑ᶠ (λ i → ν (O i))
  ν-⋃ᵒ O = ⨆-lub (λ n → μ0 (T (⋃ᵒ O) n)) (ν-inc (⋃ᵒ O)) go
    where
      go : ∀ N → μ0 (T (⋃ᵒ O) N) ≤ ∑ᶠ (λ i → ν (O i))
      go N = ≤-trans (bigU-μ0 (λ i → T (O i) N) N)
        (≤-trans (psum-mono (λ i → ν-ub (O i) N) N) (psum≤∑ᶠ (λ i → ν (O i)) N))

  ∈-⋃ᵒ← : ∀ O i {x} → x ∈ᵒ O i → x ∈ᵒ ⋃ᵒ O
  ∈-⋃ᵒ← O i {x} (n , e) = N , bigU-in (λ j → T (O j) N) x (ℕₚ.m≤n⊔m n (suc i)) (T-mono≤ O′ (ℕₚ.m≤m⊔n n (suc i)) x e)
    where N = n ⊔ suc i
          O′ = O i

  finI : (ℕ → Op) → ℕ → Op
  finI P zero = clopen (leaf true)
  finI P (suc N) = finI P N ∩ᵒ P N

  ∈-finI← : ∀ P N {x} → (∀ i → i < N → x ∈ᵒ P i) → x ∈ᵒ finI P N
  ∈-finI← P zero h = 0 , ≡.refl
  ∈-finI← P (suc N) {x} h = ∈-∩ᵒ← {finI P N} {P N} (∈-finI← P N (λ i lt → h i (ℕₚ.m<n⇒m<1+n lt))) (h N (ℕₚ.n<1+n N))

  ----------------------------------------------------------------------------
  -- complements of measures, and the measure of a finite intersection

  cmpν : Op → ∣A∣
  cmpν O = proj₁ (complement (ν-≤1 O))

  cmpν-eq : ∀ O → ν O + cmpν O ≈ 1#
  cmpν-eq O = proj₂ (complement (ν-≤1 O))

  module _ (P : ℕ → Op) (cov : ∀ N x → x ∈ᵒ finI P N ⊎ x ∈ᵒ P N) where

    ν-finI : ∀ N → ν (finI P N) + psum (λ i → cmpν (P i)) N ≈ 1#
    ν-finI zero = trans (+-cong (ν-clopen (leaf true)) refl) (+-identityʳ 1#)
    ν-finI (suc N) = cancel {1#} ≤-refl (begin
      1# + (ν (finI P N ∩ᵒ P N) + (S + c))
        ≈⟨ sym (+-assoc _ _ _) ⟩
      (1# + ν (finI P N ∩ᵒ P N)) + (S + c)
        ≈⟨ +-cong (trans (+-cong (sym (ν-cover₁ Q Pn (cov N))) refl) (ν-mod Q Pn)) refl ⟩
      (ν Q + ν Pn) + (S + c)
        ≈⟨ swap4 _ _ _ _ ⟩
      (ν Q + S) + (ν Pn + c)
        ≈⟨ +-cong (ν-finI N) (cmpν-eq Pn) ⟩
      1# + 1# ∎)
      where
        Q = finI P N
        Pn = P N
        S = psum (λ i → cmpν (P i)) N
        c = cmpν Pn
