{-# OPTIONS --safe --without-K #-}

-- Regular sets and the σ-additive extension of the fair-coin premeasure to all Borel sets.
--
-- `Meas U m` says that `m` is the measure of `U`: for every n there are opens O ⊇ U and
-- P ⊇ Uᶜ with ν O ≤ m + 2⁻ⁿ and ν P + m ≤ 1 + 2⁻ⁿ (inner and outer regularity at once).  The
-- values m are unique, the clopen sets have their dyadic measure, regular sets are closed under
-- complements and countable disjoint unions (with additive measures), hence by Dynkin's π–λ
-- theorem every Borel set is regular.  This is Carathéodory's extension theorem for Cantor
-- space, phrased with open approximations only (so only suprema of chains are needed).
module QBS.Analysis.Regular where

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

open import QBS.Borel.Core
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda
open import QBS.Analysis.Omega
open import QBS.Analysis.Series
open import QBS.Analysis.Archimedean
open import QBS.Analysis.Clopen
open import QBS.Analysis.ClopenMeasure
open import QBS.Analysis.OpenMeasure
open import QBS.Classical using (LEM₀)

module Regularity {A : OmegaSemiring (L.suc L.zero)} (R : Arch A)
    (lem : LEM₀) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R
  open Premeasure R
  open Series A
  open ArchLemmas R
  open Opens R lem
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring using (solve; _:+_; _:*_; _:=_; con)

  -- the clopen set of a tree, as a predicate
  Pt : Cl → Pred
  Pt C x = eval C x ≡ true

  record Appr (U : Pred) (m : ∣A∣) (n : ℕ) : Set₁ where
    constructor appr
    field
      aO aP : Op
      asO : ∀ x → U x → x ∈ᵒ aO
      asP : ∀ x → (U x → ⊥) → x ∈ᵒ aP
      abO : ν aO ≤ m + hp n
      abP : ν aP + m ≤ 1# + hp n
  open Appr

  Meas : Pred → ∣A∣ → Set₁
  Meas U m = ∀ n → Appr U m n

  meas-resp : ∀ {U V m} → U ≐ V → Meas U m → Meas V m
  meas-resp e M n with M n
  ... | appr O P sO sP bO bP =
    appr O P (λ x v → sO x (proj₂ (e x) v)) (λ x nv → sP x (λ u → nv (proj₁ (e x) u))) bO bP

  meas-≤1 : ∀ {U m} → Meas U m → m ≤ 1#
  meas-≤1 M = arch (λ n → ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (+-comm _ _))) (abP (M n)))

  -- uniqueness of the measure
  meas-≤ : ∀ {U m m′} → Meas U m → Meas U m′ → m′ ≤ m
  meas-≤ {U} {m} {m′} M M′ = arch go
    where
      go : ∀ k → m′ ≤ m + hp k
      go k with M (suc k) | M′ (suc k)
      ... | appr O _ sO _ bO _ | appr _ P′ _ sP′ _ bP′ =
        cancel≤ {1#} ≤-refl (≤-trans
          (≤-trans (+-mono (ν-cover O P′ cov) ≤-refl) (≤-reflexive (+-assoc _ _ _)))
          (≤-trans (+-mono bO bP′) (≤-reflexive eq)))
        where
          cov : ∀ x → x ∈ᵒ O ⊎ x ∈ᵒ P′
          cov x with lem (U x)
          ... | inj₁ u = inj₁ (sO x u)
          ... | inj₂ nu = inj₂ (sP′ x nu)
          eq : (m + hp (suc k)) + (1# + hp (suc k)) ≈ 1# + (m + hp k)
          eq = begin
            (m + hp (suc k)) + (1# + hp (suc k))
                ≈⟨ solve 3 (λ a b c → (a :+ b) :+ (c :+ b) := c :+ (a :+ (b :+ b))) refl m (hp (suc k)) 1# ⟩
            1# + (m + (hp (suc k) + hp (suc k)))  ≈⟨ +-cong refl (+-cong refl (hp-double k)) ⟩
            1# + (m + hp k) ∎

  meas-unique : ∀ {U m m′} → Meas U m → Meas U m′ → m ≈ m′
  meas-unique M M′ = ≤-antisym (meas-≤ M′ M) (meas-≤ M M′)

  -- complements
  cmp : ∀ {U m} → Meas U m → ∣A∣
  cmp M = proj₁ (complement (meas-≤1 M))

  cmp-eq : ∀ {U m} (M : Meas U m) → m + cmp M ≈ 1#
  cmp-eq M = proj₂ (complement (meas-≤1 M))

  meas-compl : ∀ {U m} (M : Meas U m) → Meas (∁ U) (cmp M)
  meas-compl {U} {m} M n with M n
  ... | appr O P sO sP bO bP = appr P O sP sO′ bP′ bO′
    where
      sO′ : ∀ x → (∁ U x → ⊥) → x ∈ᵒ O
      sO′ x nn with lem (U x)
      ... | inj₁ u = sO x u
      ... | inj₂ nu = ⊥-elim (nn nu)
      bP′ : ν P ≤ cmp M + hp n
      bP′ = cancel≤ {m} (meas-≤1 M) (≤-trans (≤-reflexive (+-comm _ _))
        (≤-trans bP (≤-reflexive (begin
          1# + hp n               ≈⟨ +-cong (sym (cmp-eq M)) refl ⟩
          (m + cmp M) + hp n      ≈⟨ +-assoc _ _ _ ⟩
          m + (cmp M + hp n)      ∎))))
      bO′ : ν O + cmp M ≤ 1# + hp n
      bO′ = ≤-trans (+-mono bO ≤-refl) (≤-reflexive (begin
        (m + hp n) + cmp M        ≈⟨ solve 3 (λ a b c → (a :+ b) :+ c := (a :+ c) :+ b) refl m (hp n) (cmp M) ⟩
        (m + cmp M) + hp n        ≈⟨ +-cong (cmp-eq M) refl ⟩
        1# + hp n                 ∎))

  -- clopen sets have their dyadic measure
  meas-clopen : ∀ C → Meas (Pt C) (μ0 C)
  meas-clopen C n = appr (clopen C) (clopen (∁ᶜ C)) (λ x e → 0 , e) sP
    (≤-trans (≤-reflexive (ν-clopen C)) ≤-+ʳ)
    (≤-trans (≤-reflexive (trans (+-cong (ν-clopen (∁ᶜ C)) refl) (μ0-∁ C))) ≤-+ʳ)
    where
      sP : ∀ x → (Pt C x → ⊥) → x ∈ᵒ clopen (∁ᶜ C)
      sP x nt = 0 , ≡.trans (eval-∁ C x) (≡.cong not (¬true⇒false _ nt))

  -- the tree of the cylinder {x | x n ≡ b}
  bitT : ℕ → Bool → Cl
  bitT zero b = split (leaf (not b)) (leaf b)
  bitT (suc n) b = split (bitT n b) (bitT n b)

  eval-bitT : ∀ n b x → eval (bitT n b) x ≡ true → x n ≡ b
  eval-bitT zero b x e with x 0 | e
  eval-bitT zero true x e | true | _ = ≡.refl
  eval-bitT zero false x e | false | _ = ≡.refl
  eval-bitT (suc n) b x e with x 0
  ... | false = eval-bitT n b (tl x) e
  ... | true = eval-bitT n b (tl x) e

  bitT-eval : ∀ n b x → x n ≡ b → eval (bitT n b) x ≡ true
  bitT-eval zero b x e with x 0
  bitT-eval zero true x ≡.refl | true = ≡.refl
  bitT-eval zero false x ≡.refl | false = ≡.refl
  bitT-eval (suc n) b x e with x 0
  ... | false = bitT-eval n b (tl x) e
  ... | true = bitT-eval n b (tl x) e

  cyl→tree : ∀ {U} → Cyl U → Σ Cl (λ C → U ≐ Pt C)
  cyl→tree cylTop = leaf true , (λ x → (λ _ → ≡.refl) , (λ _ → _))
  cyl→tree (cylAnd {U} c n b) with cyl→tree c
  ... | C , e = C ∩ bitT n b , λ x →
      (λ { (u , xb) → ≡.trans (eval-∩ C (bitT n b) x) (and-intro (proj₁ (e x) u) (bitT-eval n b x xb)) })
    , (λ t → let cx , bx = and-elim _ _ (≡.trans (≡.sym (eval-∩ C (bitT n b) x)) t)
             in proj₂ (e x) cx , eval-bitT n b x bx)
  cyl→tree (cylResp {U} {V} e c) with cyl→tree c
  ... | C , e′ = C , ≐-trans (≐-sym e) e′

  meas-cyl : ∀ {U} → Cyl U → Σ ∣A∣ (Meas U)
  meas-cyl c with cyl→tree c
  ... | C , e = μ0 C , meas-resp (≐-sym e) (meas-clopen C)

  ----------------------------------------------------------------------------
  -- countable disjoint unions

  module Union (U : ℕ → Pred) (dj : Disjoint U) (m : ℕ → ∣A∣) (ms : ∀ i → Meas (U i) (m i)) where

    UU : Pred
    UU x = Σ ℕ (λ i → U i x)

    -- approximations of the i-th set to the tolerance 2^-(i+1+k)
    module AtTol (k : ℕ) where
      D : ∀ i → Appr (U i) (m i) (suc i ℕ.+ k)
      D i = ms i (suc i ℕ.+ k)

      Oi Pi : ℕ → Op
      Oi i = aO (D i)
      Pi i = aP (D i)

      ε : ℕ → ∣A∣
      ε i = hp (suc i ℕ.+ k)

      cov : ∀ N x → x ∈ᵒ finI Pi N ⊎ x ∈ᵒ Pi N
      cov N x with lem (x ∈ᵒ Pi N)
      ... | inj₂ nP = inj₁ (∈-finI← Pi N all)
        where
          UN : U N x
          UN with lem (U N x)
          ... | inj₁ u = u
          ... | inj₂ nu = ⊥-elim (nP (asP (D N) x nu))
          all : ∀ i → i < N → x ∈ᵒ Pi i
          all i lt = asP (D i) x (λ u → ℕₚ.<-irrefl ≡.refl (subst′ lt (dj x i N u UN)))
            where subst′ : ∀ {i N} → i < N → i ≡ N → N < N
                  subst′ lt ≡.refl = lt
      ... | inj₁ yes = inj₂ yes

      -- m i ≤ cmpν (Pi i) + ε i
      m≤cmp : ∀ i → m i ≤ cmpν (Pi i) + ε i
      m≤cmp i = cancel≤ {ν (Pi i)} (ν-≤1 (Pi i))
        (≤-trans (abP (D i)) (≤-reflexive (begin
          1# + ε i                           ≈⟨ +-cong (sym (cmpν-eq (Pi i))) refl ⟩
          (ν (Pi i) + cmpν (Pi i)) + ε i     ≈⟨ +-assoc _ _ _ ⟩
          ν (Pi i) + (cmpν (Pi i) + ε i)     ∎)))

      psum-m≤ : ∀ N → psum m N ≤ psum (λ i → cmpν (Pi i)) N + psum ε N
      psum-m≤ N = ≤-trans (psum-mono m≤cmp N) (≤-reflexive (psum-+ (λ i → cmpν (Pi i)) ε N))

      psum-cmp≤1 : ∀ N → psum (λ i → cmpν (Pi i)) N ≤ 1#
      psum-cmp≤1 N = ≤-trans ≤-+ʳ′ (≤-reflexive (ν-finI Pi cov N))
        where ≤-+ʳ′ : psum (λ i → cmpν (Pi i)) N ≤ ν (finI Pi N) + psum (λ i → cmpν (Pi i)) N
              ≤-+ʳ′ = ≤-trans (≤-reflexive (sym (+-identityˡ _))) (+-mono 0-least ≤-refl)

      psum-ε≤ : ∀ N → psum ε N ≤ hp k
      psum-ε≤ N = ≤-trans (psum≤∑ᶠ ε N) (geo-sum k)

    psum-m≤1 : ∀ N → psum m N ≤ 1#
    psum-m≤1 N = arch (λ k → ≤-trans (AtTol.psum-m≤ k N)
      (+-mono (AtTol.psum-cmp≤1 k N) (AtTol.psum-ε≤ k N)))

    M : ∣A∣
    M = ∑ᶠ m

    M≤1 : M ≤ 1#
    M≤1 = ∑ᶠ-lub psum-m≤1

    meas-union : Meas UU M
    meas-union n with way-below (psum m) (psum-inc m) M≤1 (suc n)
    ... | N , wb = appr O P sO sP bO bP
      where
        k = suc n
        open AtTol k
        O P : Op
        O = ⋃ᵒ Oi
        P = finI Pi N
        sO : ∀ x → UU x → x ∈ᵒ O
        sO x (i , u) = ∈-⋃ᵒ← Oi i (asO (D i) x u)
        sP : ∀ x → (UU x → ⊥) → x ∈ᵒ P
        sP x nu = ∈-finI← Pi N (λ i lt → asP (D i) x (λ u → nu (i , u)))
        bO : ν O ≤ M + hp n
        bO = ≤-trans (ν-⋃ᵒ Oi)
          (≤-trans (∑ᶠ-mono (λ i → abO (D i)))
            (≤-trans (≤-reflexive (∑ᶠ-+ m ε))
              (+-mono ≤-refl (≤-trans (geo-sum k) (hp-≤ n)))))
        bP : ν P + M ≤ 1# + hp n
        bP = ≤-trans (+-mono ≤-refl wb)
          (≤-trans (+-mono ≤-refl (+-mono (psum-m≤ N) ≤-refl))
            (≤-trans (≤-reflexive (solve 4 (λ x s e h → x :+ ((s :+ e) :+ h) := (x :+ s) :+ (e :+ h)) refl
                 (ν P) (psum (λ i → cmpν (Pi i)) N) (psum ε N) (hp k)))
              (≤-trans (≤-reflexive (+-cong (ν-finI Pi cov N) refl))
                (≤-trans (+-mono ≤-refl (+-mono (psum-ε≤ N) ≤-refl))
                  (≤-reflexive (+-cong refl (hp-double n)))))))

  ----------------------------------------------------------------------------
  -- every Borel set is regular

  open Dynkin lem using (dynkin)

  Good : Pred → Set₁
  Good U = Σ ∣A∣ (Meas U)

  good-resp : ∀ {U V} → U ≐ V → Good U → Good V
  good-resp e (m , M) = m , meas-resp e M

  good-cyl : ∀ {U} → Cyl U → Good U
  good-cyl = meas-cyl

  good-compl : ∀ {U} → Good U → Good (∁ U)
  good-compl (m , M) = cmp M , meas-compl M

  good-union : ∀ {U : ℕ → Pred} → (∀ n → Good (U n)) → Disjoint U → Good (λ x → Σ ℕ (λ n → U n x))
  good-union {U} ds dj = Union.M U dj m ms , Union.meas-union U dj m ms
    where
      m : ℕ → ∣A∣
      m i = proj₁ (ds i)
      ms : ∀ i → Meas (U i) (m i)
      ms i = proj₂ (ds i)

  borel-meas : ∀ {U} → Borel U → Good U
  borel-meas {U} b = dynkin Good (λ {V} {W} → good-resp {V} {W}) good-cyl
    (λ {V} → good-compl {V}) (λ {V} → good-union {V}) b

  -- the measure of a Borel set (abstract: only its characterisation `μ-meas` is used)
  abstract
    μ : ∀ {U} → Borel U → ∣A∣
    μ {U} b = proj₁ (borel-meas {U} b)

    μ-meas : ∀ {U} (b : Borel U) → Meas U (μ b)
    μ-meas {U} b = proj₂ (borel-meas {U} b)

  μ-unique : ∀ {U m} (b : Borel U) → Meas U m → μ b ≈ m
  μ-unique {U} {m} b M = meas-unique {U} (μ-meas b) M

  μ-resp : ∀ {U V} (bU : Borel U) (bV : Borel V) → U ≐ V → μ bU ≈ μ bV
  μ-resp {U} {V} bU bV e = μ-unique bU (meas-resp {V} {U} (≐-sym e) (μ-meas bV))

  μ-compl : ∀ {U} (b : Borel U) → μ b + μ (compl b) ≈ 1#
  μ-compl {U} b = trans (+-cong refl (μ-unique (compl b) (meas-compl (μ-meas b)))) (cmp-eq (μ-meas b))

  μ-cyl : ∀ {U} (c : Cyl U) (b : Borel U) → μ b ≈ μ0 (proj₁ (cyl→tree c))
  μ-cyl {U} c b = μ-unique b (proj₂ (meas-cyl c))

  μ-≤1 : ∀ {U} (b : Borel U) → μ b ≤ 1#
  μ-≤1 {U} b = meas-≤1 (μ-meas b)

  μ-⋃ : ∀ {U : ℕ → Pred} (bs : ∀ n → Borel (U n)) (dj : Disjoint U) →
    μ (⋃ bs) ≈ ∑ᶠ (λ n → μ (bs n))
  μ-⋃ {U} bs dj = μ-unique (⋃ bs) (Union.meas-union U dj (λ n → μ (bs n)) (λ n → μ-meas (bs n)))
