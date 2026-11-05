{-# OPTIONS --safe --without-K #-}

-- Convergence with explicit tolerances, and convergence of differences (plan 03, "Signed dominated convergence").
--   * `EConv a l`: for every k, eventually a n ≤ l + ½ᵏ and l ≤ a n + ½ᵏ;  `conv-econv`/`econv-conv`: for finite l
--     this is `Dominated.Conv` (lim inf ≈ lim sup ≈ l);
--   * `SConv a b u v`: "a n − b n → u − v" without subtraction: for every k, eventually a n + v ≤ u + b n + ½ᵏ and
--     u + b n ≤ a n + v + ½ᵏ;  `sconv-pair`: if a → u and b → v then a − b → u − v;  `sconv-shift`: adding the same
--     sequence to both sides of a difference (c n + d n with d → 0) keeps the limit.
-- Route: `econv-conv` with `LowerRealsNear.inter-add` and `Arch.arch`; `conv-econv` needs, for a decreasing
-- sequence of tail suprema whose infimum is ≤ l, one tail ≤ l + ½ᵏ: by excluded middle, otherwise a rational strictly
-- above l lies in every tail, hence in the infimum (`LowerRealsNear.near-sup-bnd` gives a rational near l).
-- `sconv-pair` with ½ᵏ⁺¹ + ½ᵏ⁺¹ ≈ ½ᵏ (`Half`).
module QBS.Continuous.ConvEps where

open import Data.Nat.Base using (ℕ; suc; _≤_) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Nat.Base using (_∸_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Rational.Unnormalised.Base using (ℚᵘ)
  renaming (_+_ to _+ℚ_; _≤_ to _≤ℚ_; _<_ to _<ℚ_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.LowerReals using (Cut; module Cut; unionC; _⊑_; mk⊑; module _⊑_; ⊑-refl; ⊑-trans; ⊕-mono; union-ub; union-lub)
open import QBS.Analysis.LowerRealsInf using (interC; liminfC; limsupC; inter-lb; liminf-limsup)
open import QBS.Analysis.LowerRealsNear using (module Near)
open import QBS.Analysis.LowerRealsArch using (tp; tp-pos; tp-lt)
open import QBS.Analysis.RationalLemmas using (dense; ≤-or->; ≃-refl; <-irrefl; <-≤-trans; <-≤; ≤-trans)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Continuous.Fatou using (module Fatou)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Dominated using (module Dominated)

open Cut using (mem; down)
open _⊑_ using (ap)

module ConvEps (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; 0#; +-assoc; +-comm; +-cong; +-identityʳ; +-mono; ≤-+ʳ;
    refl; sym; trans; ≤-reflexive; setoid)
    renaming (Carrier to ∣A∣; _≤_ to _≤ᴬ_; ≤-trans to ≤ᴬ-trans; ≤-refl to ≤ᴬ-refl)
  open Bounded A using (Bnd)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half; arch) renaming (half+half to hh)
  open Half A half hh using (hp; hp-double)
  open Dominated lem₁ using (Conv)
  open Fatou lem₁ using (hp-in; BndQ-hp)
  open Near (lemOf lem₁) using (near-sup-bnd; inter-add)
  open LebesgueShiftAlg (lemOf lem₁) using (bnd-rat)
  open SetoidReasoning setoid

  -- n = N + j when N ≤ n
  tail : ∀ {N n} → N ≤ n → Σ ℕ (λ j → N +ℕ j ≡ n)
  tail {N} {n} le = n ∸ N , ℕP.m+[n∸m]≡n le

  -- a tail bound transfers to the index N + j
  at-tail : ∀ {N} (P : ℕ → Set₁) → (∀ j → P (N +ℕ j)) → ∀ n → N ≤ n → P n
  at-tail P h n le = subst P (proj₂ (tail le)) (h (proj₁ (tail le)))

  -- the classical step: if not every P n holds, some P n fails
  not-all : ∀ (P : ℕ → Set) → ¬ (∀ n → P n) → Σ ℕ (λ n → ¬ P n)
  not-all P h with lemOf lem₁ (Σ ℕ (λ n → ¬ P n))
  ... | inj₁ yes = yes
  ... | inj₂ none = ⊥-elim (h (λ n → help n (lemOf lem₁ (P n))))
    where help : ∀ n → P n ⊎ ¬ P n → P n
          help n (inj₁ p) = p
          help n (inj₂ np) = ⊥-elim (none (n , np))

  -- a n → l, with tolerance ½ᵏ from some index on
  EConv : (ℕ → ∣A∣) → ∣A∣ → Set₁
  EConv a l = ∀ k → Σ ℕ (λ N → ∀ n → N ≤ n → (a n ≤ᴬ l + hp k) × (l ≤ᴬ a n + hp k))

  -- from EConv: lim sup a ≤ l + ½ᵏ and l ≤ lim inf a + ½ᵏ
  limsup-tol : ∀ a l k N → (∀ n → N ≤ n → a n ≤ᴬ l + hp k) → limsupC a ⊑ l + hp k
  limsup-tol a l k N h = ⊑-trans (inter-lb _ N) (union-lub _ (λ j → h (N +ℕ j) (ℕP.m≤m+n N j)))

  liminf-tol : ∀ a l k N → (∀ n → N ≤ n → l ≤ᴬ a n + hp k) → l ≤ᴬ liminfC a + hp k
  liminf-tol a l k N h = ⊑-trans (inter-add {l} {λ j → a (N +ℕ j)} (BndQ-hp k) (λ j → h (N +ℕ j) (ℕP.m≤m+n N j)))
    (⊕-mono (union-ub (λ n → interC (λ j → a (n +ℕ j))) N) ⊑-refl)

  econv-conv : ∀ a l → EConv a l → Conv a l
  econv-conv a l ec = (⊑-trans (liminf-limsup a) ls , li) , (ls , ⊑-trans li (liminf-limsup a))
    where
      ls : limsupC a ≤ᴬ l
      ls = arch (λ k → limsup-tol a l k (proj₁ (ec k)) (λ n le → proj₁ (proj₂ (ec k) n le)))
      li : l ≤ᴬ liminfC a
      li = arch (λ k → liminf-tol a l k (proj₁ (ec k)) (λ n le → proj₂ (proj₂ (ec k) n le)))

  -- an element of l close to its supremum
  close : ∀ l → Bnd l → ∀ k → Σ ℚᵘ (λ r → mem l r × (∀ r′ → mem l r′ → r′ ≤ℚ r +ℚ tp (suc (suc k))))
  close l bl k = near-sup-bnd l (proj₁ (bnd-rat l bl)) (proj₂ (bnd-rat l bl)) (tp-pos (suc (suc k)))

  -- a near-supremum r of l lying in the N-th lower tail puts l below that tail plus ½ᵏ
  low-step : ∀ (a : ℕ → Cut) l k N r → (∀ r′ → mem l r′ → r′ ≤ℚ r +ℚ tp (suc (suc k))) →
    mem (interC (λ i → a (N +ℕ i))) r → l ⊑ interC (λ i → a (N +ℕ i)) + hp k
  low-step a l k N r hr mN = mk⊑ (λ q mq → r , tp (suc k) , mN , hp-in k (tp (suc k)) (tp-lt k) ,
    ≤-trans (hr q mq) (ℚP.+-monoʳ-≤ r (<-≤ (tp-lt (suc k)))))

  -- l ≤ lim inf a gives a tail with l ≤ a n + ½ᵏ
  low-tail : ∀ a l → Bnd l → l ≤ᴬ liminfC a → ∀ k → Σ ℕ (λ N → ∀ n → N ≤ n → l ≤ᴬ a n + hp k)
  low-tail a l bl li k = low-tail′ a l k (close l bl k) li
    where
      low-tail′ : ∀ a l k → Σ ℚᵘ (λ r → mem l r × (∀ r′ → mem l r′ → r′ ≤ℚ r +ℚ tp (suc (suc k)))) →
        l ≤ᴬ liminfC a → Σ ℕ (λ N → ∀ n → N ≤ n → l ≤ᴬ a n + hp k)
      low-tail′ a l k (r , mr , hr) li = proj₁ mN , at-tail {proj₁ mN} (λ n → l ≤ᴬ a n + hp k) (λ j →
        ⊑-trans {l} {interC (λ i → a (proj₁ mN +ℕ i)) + hp k} {a (proj₁ mN +ℕ j) + hp k}
          (low-step a l k (proj₁ mN) r hr (proj₂ mN))
          (⊕-mono {interC (λ i → a (proj₁ mN +ℕ i))} {a (proj₁ mN +ℕ j)} {hp k} {hp k}
            (inter-lb (λ i → a (proj₁ mN +ℕ i)) j) ⊑-refl))
        where mN = ap li r mr

  -- if r + s were in every tail of the lim sup, it would exceed the near-supremum of l
  no-all : ∀ a l → limsupC a ≤ᴬ l → ∀ k r s → (∀ r′ → mem l r′ → r′ ≤ℚ r +ℚ tp (suc (suc k))) → tp (suc k) <ℚ s →
    ¬ (∀ N → mem (unionC (λ j → a (N +ℕ j))) (r +ℚ s))
  no-all a l ls k r s hr st all = <-irrefl ≃-refl (<-≤-trans (ℚP.+-monoʳ-< r (tp-lt (suc k)))
    (hr _ (ap ls _ (_ , ℚP.+-monoʳ-< r st , all))))

  -- below r + s ≤ r + ½ᵏ, outside the failing tail, the tail lies in l + ½ᵏ
  cut-step : ∀ (a : ℕ → Cut) (l : Cut) (k N : ℕ) (r s : ℚᵘ) → mem l r → s <ℚ tp k → ¬ mem (unionC (λ i → a (N +ℕ i))) (r +ℚ s) →
    unionC (λ i → a (N +ℕ i)) ⊑ l + hp k
  cut-step a l k N r s mr ts nN = mk⊑ (λ q mq → go q mq (≤-or-> q (r +ℚ s)))
    where
      go : ∀ q → mem (unionC (λ i → a (N +ℕ i))) q → q ≤ℚ r +ℚ s ⊎ r +ℚ s <ℚ q → mem (l + hp k) q
      go q mq (inj₁ le) = r , s , mr , hp-in k s ts , le
      go q mq (inj₂ lt) = ⊥-elim (nN (down (unionC (λ i → a (N +ℕ i))) (<-≤ lt) mq))

  -- lim sup a ≤ l gives a tail with a n ≤ l + ½ᵏ
  up-tail : ∀ a l → Bnd l → limsupC a ≤ᴬ l → ∀ k → Σ ℕ (λ N → ∀ n → N ≤ n → a n ≤ᴬ l + hp k)
  up-tail a l bl ls k = up-tail′ a l ls k (close l bl k) (dense (tp-lt k))
    where
      up-tail′ : ∀ (a : ℕ → Cut) (l : Cut) → limsupC a ≤ᴬ l → ∀ k →
        Σ ℚᵘ (λ r → mem l r × (∀ r′ → mem l r′ → r′ ≤ℚ r +ℚ tp (suc (suc k))))  →
        Σ ℚᵘ (λ s → tp (suc k) <ℚ s × s <ℚ tp k) → Σ ℕ (λ N → ∀ n → N ≤ n → a n ≤ᴬ l + hp k)
      up-tail′ a l ls k (r , mr , hr) (s , st , ts) = proj₁ nn , at-tail {proj₁ nn} (λ n → a n ≤ᴬ l + hp k)
        (λ j → ⊑-trans {a (proj₁ nn +ℕ j)} {unionC (λ i → a (proj₁ nn +ℕ i))} {l + hp k}
          (union-ub (λ i → a (proj₁ nn +ℕ i)) j) (cut-step a l k (proj₁ nn) r s mr ts (proj₂ nn)))
        where nn = not-all _ (no-all a l ls k r s hr st)

  conv-econv : ∀ a l → Bnd l → Conv a l → EConv a l
  conv-econv a l bl (li , ls) k = N₁ +ℕ N₂ , λ n le →
    proj₂ (up-tail a l bl (proj₁ ls) k) n (ℕP.≤-trans (ℕP.m≤n+m N₂ N₁) le) ,
    proj₂ (low-tail a l bl (proj₂ li) k) n (ℕP.≤-trans (ℕP.m≤m+n N₁ N₂) le)
    where
      N₁ = proj₁ (low-tail a l bl (proj₂ li) k)
      N₂ = proj₁ (up-tail a l bl (proj₁ ls) k)

  -- a n − b n → u − v
  SConv : (ℕ → ∣A∣) → (ℕ → ∣A∣) → ∣A∣ → ∣A∣ → Set₁
  SConv a b u v = ∀ k → Σ ℕ (λ N → ∀ n → N ≤ n → (a n + v ≤ᴬ u + b n + hp k) × (u + b n ≤ᴬ a n + v + hp k))

  -- adding two tolerance bounds
  add-tol : ∀ {x y z w} k → x ≤ᴬ y + hp (suc k) → z ≤ᴬ w + hp (suc k) → x + z ≤ᴬ (y + w) + hp k
  add-tol {x} {y} {z} {w} k p q = ≤ᴬ-trans (OmegaSemiring.+-mono A p q) (≤-reflexive (begin
    (y + h) + (w + h)  ≈⟨ +-assoc y h (w + h) ⟩
    y + (h + (w + h))  ≈⟨ +-cong refl (trans (sym (+-assoc h w h)) (trans (+-cong (+-comm h w) refl) (+-assoc w h h))) ⟩
    y + (w + (h + h))  ≈⟨ sym (+-assoc y w (h + h)) ⟩
    (y + w) + (h + h)  ≈⟨ +-cong refl (hp-double k) ⟩
    (y + w) + hp k ∎))
    where h = hp (suc k)

  sconv-pair : ∀ a b u v → EConv a u → EConv b v → SConv a b u v
  sconv-pair a b u v ea eb k with ea (suc k) | eb (suc k)
  ... | N₁ , h₁ | N₂ , h₂ = N₁ +ℕ N₂ , λ n le →
    let le₁ = ℕP.≤-trans (ℕP.m≤m+n N₁ N₂) le ; le₂ = ℕP.≤-trans (ℕP.m≤n+m N₂ N₁) le
    in add-tol k (proj₁ (h₁ n le₁)) (proj₂ (h₂ n le₂)) , add-tol k (proj₂ (h₁ n le₁)) (proj₁ (h₂ n le₂))

  -- the two cross inequalities for shifted sequences
  shift₁ : ∀ {a b d e u v} k → a + v ≤ᴬ u + b + hp (suc k) → d ≤ᴬ 0# + hp (suc k) → (a + d) + v ≤ᴬ u + (b + e) + hp k
  shift₁ {a} {b} {d} {e} {u} {v} k p q = ≤ᴬ-trans (≤-reflexive swap) (≤ᴬ-trans (add-tol k p q) (+-mono step ≤ᴬ-refl))
    where
      swap = trans (+-assoc a d v) (trans (+-cong refl (+-comm d v)) (sym (+-assoc a v d)))
      step : (u + b) + 0# ≤ᴬ u + (b + e)
      step = ≤ᴬ-trans (≤-reflexive (+-identityʳ _)) (≤ᴬ-trans ≤-+ʳ (≤-reflexive (+-assoc u b e)))

  shift₂ : ∀ {a b d e u v} k → u + b ≤ᴬ a + v + hp (suc k) → e ≤ᴬ 0# + hp (suc k) → u + (b + e) ≤ᴬ (a + d) + v + hp k
  shift₂ {a} {b} {d} {e} {u} {v} k p q = ≤ᴬ-trans (≤-reflexive (sym (+-assoc u b e)))
    (≤ᴬ-trans (add-tol k p q) (+-mono step ≤ᴬ-refl))
    where
      step : (a + v) + 0# ≤ᴬ (a + d) + v
      step = ≤ᴬ-trans (≤-reflexive (+-identityʳ _)) (+-mono ≤-+ʳ ≤ᴬ-refl)

  -- (a n + d n) − (b n + e n) → u − v when a − b → u − v and d, e → 0
  sconv-shift : ∀ a b d e u v → SConv a b u v → EConv d 0# → EConv e 0# →
    SConv (λ n → a n + d n) (λ n → b n + e n) u v
  sconv-shift a b d e u v sc ed ee k with sc (suc k) | ed (suc k) | ee (suc k)
  ... | N₁ , h₁ | N₂ , h₂ | N₃ , h₃ = N₁ +ℕ (N₂ +ℕ N₃) , λ n le →
    let l₁ = ℕP.≤-trans (ℕP.m≤m+n N₁ _) le
        l₂ = ℕP.≤-trans (ℕP.m≤m+n N₂ N₃) (ℕP.≤-trans (ℕP.m≤n+m _ N₁) le)
        l₃ = ℕP.≤-trans (ℕP.m≤n+m N₃ N₂) (ℕP.≤-trans (ℕP.m≤n+m _ N₁) le)
    in shift₁ k (proj₁ (h₁ n l₁)) (proj₁ (h₂ n l₂)) , shift₂ k (proj₂ (h₁ n l₁)) (proj₁ (h₃ n l₃))

