{-# OPTIONS --safe --without-K #-}

-- The inverse of a lower cut: `q < 1/c` iff `q < 0` or `q ρ < 1` for some `ρ > 0` that is not below `c`
-- (so `1/0 = ∞` and `1/∞ = 0`).  For `0 < c < ∞` it is a multiplicative inverse (classical: the
-- boundary of `c` is approximated from inside, as in `LowerReals.near-sup`).
module QBS.Analysis.LowerInverse where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
import Data.Rational.Unnormalised.Properties as P
open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut

-- the inverse of a positive rational is positive
pos-of-inverse : ∀ {ρ t} → 0ℚᵘ < ρ → t * ρ ≃ 1ℚᵘ → 0ℚᵘ < t
pos-of-inverse {ρ} {t} 0<ρ ht with pos-or-nonpos t
... | inj₁ 0<t = 0<t
... | inj₂ t≤0 = ⊥-elim (<-irrefl ≃-refl (<-≤-trans (≃-<ʳ (≃-sym ht) 0<1)
                    (≤-trans (*-mono-≤-nnʳ (<-≤ 0<ρ) t≤0) (≤-≃ (*-zeroˡ ρ)))))

-- 1 / c
invC : Cut → Cut
invC c = record
  { mem = λ q → q < 0ℚᵘ ⊎ Σ ℚᵘ (λ ρ → 0ℚᵘ < ρ × ((mem c ρ → ⊥) × q * ρ < 1ℚᵘ))
  ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt)
             ; le (inj₂ (ρ , 0<ρ , nm , pρ<1)) → inj₂ (ρ , 0<ρ , nm , ≤-<-trans (*-mono-≤-nnʳ (<-≤ 0<ρ) le) pρ<1) }
  ; open′ = open-inv
  ; neg = inj₁ }
  where
    open-inv : ∀ {p} → (p < 0ℚᵘ ⊎ Σ ℚᵘ (λ ρ → 0ℚᵘ < ρ × ((mem c ρ → ⊥) × p * ρ < 1ℚᵘ))) →
      Σ ℚᵘ (λ q → p < q × (q < 0ℚᵘ ⊎ Σ ℚᵘ (λ ρ → 0ℚᵘ < ρ × ((mem c ρ → ⊥) × q * ρ < 1ℚᵘ))))
    open-inv (inj₁ lt) = let r , p<r , r<0 = dense lt in r , p<r , inj₁ r<0
    open-inv {p} (inj₂ (ρ , 0<ρ , nm , pρ<1)) =
      let u , pρ<u , u<1 = dense pρ<1
          t , ht = inv 0<ρ
          0<t = pos-of-inverse 0<ρ ht
      in u * t , ≃-<ˡ (back p ρ t ht) (*-mono-<-posʳ 0<t pρ<u) ,
         inj₂ (ρ , 0<ρ , nm , ≃-<ˡ (≃-sym (back′ u ρ t ht)) u<1)
      where
        back : ∀ a ρ t → t * ρ ≃ 1ℚᵘ → (a * ρ) * t ≃ a
        back a ρ t ht = ≃-trans (*-assoc a ρ t) (≃-trans (*-cong (≃-refl {a}) (≃-trans (*-comm ρ t) ht)) (P.*-identityʳ a))
        back′ : ∀ u ρ t → t * ρ ≃ 1ℚᵘ → (u * t) * ρ ≃ u
        back′ u ρ t ht = ≃-trans (*-assoc u t ρ) (≃-trans (*-cong (≃-refl {u}) ht) (P.*-identityʳ u))

-- c⁻¹ · c ≤ 1
inv-mul-⊑ : ∀ c → invC c ⊗ c ⊑ oneC
inv-mul-⊑ c = mk⊑ (λ q → λ
  { (inj₁ q<0) → <-trans q<0 0<1
  ; (inj₂ (r , s , 0<r , 0<s , mr , ms , le)) → go r s 0<r mr ms le })
  where
    go : ∀ {q} r s → 0ℚᵘ < r → mem (invC c) r → mem c s → q ≤ r * s → q < 1ℚᵘ
    go r s 0<r (inj₁ r<0) ms le = ⊥-elim (<-irrefl ≃-refl (<-trans 0<r r<0))
    go r s 0<r (inj₂ (ρ , 0<ρ , nm , rρ<1)) ms le with ≤-or-> ρ s
    ... | inj₁ ρ≤s = ⊥-elim (nm (down c ρ≤s ms))
    ... | inj₂ s<ρ = ≤-<-trans le (<-trans (*-mono-<-pos 0<r s<ρ) rρ<1)

----------------------------------------------------------------------------
-- rational estimates

twice-≤ : ∀ {x y} → x + x ≤ y + y → x ≤ y
twice-≤ {x} {y} h with ≤-or-> x y
... | inj₁ le = le
... | inj₂ lt = ⊥-elim (<-irrefl ≃-refl (<-≤-trans (+-mono-< lt lt) h))

-- 4ε ≤ s + ε gives ε ≤ s
eps-le : ∀ {ε s} → 0ℚᵘ < ε → ((ε + ε) + (ε + ε)) ≤ s + ε → ε ≤ s
eps-le {ε} {s} 0<ε h4′ with ≤-or-> ε s
... | inj₁ le = le
... | inj₂ s<ε = ⊥-elim (<-irrefl ≃-refl (<-≤-trans (<-≤-trans (+-mono-<-≤ s<ε (≤-refl {ε})) εε≤4ε) h4′))
  where
    0<εε : 0ℚᵘ < ε + ε
    0<εε = ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<ε 0<ε)
    εε≤4ε : ε + ε ≤ (ε + ε) + (ε + ε)
    εε≤4ε = ≤-trans (≤-≃ (≃-sym (+-identityʳ (ε + ε)))) (+-mono-≤ (≤-refl {ε + ε}) (<-≤ 0<εε))

-- q (s + 2ε) ≤ q′ s from q ≤ 1 and 2ε ≤ (q′ − q) s
combine : ∀ {q q′ s ε} → 0ℚᵘ ≤ ε + ε → q ≤ 1ℚᵘ → ε + ε ≤ (q′ + - q) * s → q * (s + (ε + ε)) ≤ q′ * s
combine {q} {q′} {s} {ε} 0≤εε q≤1 m3 =
  ≤-trans (≤-≃ (*-distribˡ-+ q s (ε + ε))) (≤-trans (+-mono-≤ (≤-refl {q * s}) (≤-trans m2 m3)) (≤-≃ m4))
  where
    m2 : q * (ε + ε) ≤ ε + ε
    m2 = ≤-trans (*-mono-≤-nnʳ 0≤εε q≤1) (≤-≃ (*-identityˡ (ε + ε)))
    m4 : q * s + (q′ + - q) * s ≃ q′ * s
    m4 = ≃-trans (≃-sym (*-distribʳ-+ s q (q′ + - q))) (*-cong (add-sub q q′) (≃-refl {s}))

-- the choice of the approximation scale: 4ε ≤ δ s₀ makes `s` close enough to the boundary
gap : ∀ {q q′ s₀ s ε} → 0ℚᵘ ≤ q → q < q′ → q′ < 1ℚᵘ → 0ℚᵘ < s₀ → 0ℚᵘ < ε →
  ((ε + ε) + (ε + ε)) ≤ (q′ + - q) * s₀ → s₀ ≤ s + ε →
  (0ℚᵘ < s) × (q * (s + (ε + ε)) ≤ q′ * s)
gap {q} {q′} {s₀} {s} {ε} 0≤q q<q′ q′<1 0<s₀ 0<ε h4 hs = 0<s , combine {q} {q′} {s} {ε} (<-≤ 0<εε) (<-≤ (<-trans q<q′ q′<1)) m3
  where
    δ = q′ + - q
    0<δ : 0ℚᵘ < δ
    0<δ = pos-diff q<q′
    δ≤1 : δ ≤ 1ℚᵘ
    δ≤1 = ≤-trans (≤-≃ (≃-sym (+-identityʳ δ)))
            (≤-trans (+-mono-≤ (≤-refl {δ}) 0≤q) (≤-trans (≤-≃ (sub-add q′ q)) (<-≤ q′<1)))
    δs₀≤s₀ : δ * s₀ ≤ s₀
    δs₀≤s₀ = ≤-trans (*-mono-≤-nnʳ (<-≤ 0<s₀) δ≤1) (≤-≃ (*-identityˡ s₀))
    0<εε : 0ℚᵘ < ε + ε
    0<εε = ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<ε 0<ε)
    -- 4ε ≤ s₀ ≤ s + ε, so ε ≤ s and 0 < s
    ε≤s : ε ≤ s
    ε≤s = eps-le 0<ε (≤-trans h4 (≤-trans δs₀≤s₀ hs))
    0<s : 0ℚᵘ < s
    0<s = <-≤-trans 0<ε ε≤s
    s₀≤ss : s₀ ≤ s + s
    s₀≤ss = ≤-trans hs (+-mono-≤ (≤-refl {s}) ε≤s)
    m3 : ε + ε ≤ δ * s
    m3 = twice-≤ (≤-trans h4 (≤-trans (*-mono-≤-nn (<-≤ 0<δ) s₀≤ss) (≤-≃ (*-distribˡ-+ δ s s))))

-- `q ≤ r s` from `r ρ ≃ q′` and `q ρ ≤ q′ s`.  A standalone lemma: the `with` on `≤-or->` used to sit in the
-- local context of `InvClassical.inv-prop` and took 14 s there.
le-of-scaled : ∀ {q r s ρ q′} → 0ℚᵘ < ρ → r * ρ ≃ q′ → q * ρ ≤ q′ * s → q ≤ r * s
le-of-scaled {q} {r} {s} {ρ} {q′} 0<ρ rρ qρ≤q′s with ≤-or-> q (r * s)
... | inj₁ le = le
... | inj₂ rs<q = ⊥-elim (<-irrefl ≃-refl (<-≤-trans
      (≃-<ˡ (≃-trans swap (*-cong rρ (≃-refl {s}))) (*-mono-<-posʳ 0<ρ rs<q)) qρ≤q′s))
  where
    swap : (r * s) * ρ ≃ (r * ρ) * s
    swap = ≃-trans (*-assoc r s ρ) (≃-trans (*-cong (≃-refl {r}) (P.*-comm s ρ)) (≃-sym (*-assoc r ρ s)))

----------------------------------------------------------------------------
-- the boundary of a bounded cut is approximated by its elements (classical)

open import Data.Sum.Base using ()

module InvClassical (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

  near-sup′ : ∀ c M → (∀ r → mem c r → r < M) → ∀ {ε} → 0ℚᵘ < ε →
    Σ ℚᵘ (λ r → mem c r × (∀ r′ → mem c r′ → r′ ≤ r + ε))
  near-sup′ c M bd {ε} 0<ε with lem (Σ ℚᵘ (λ r → mem c r × (∀ r′ → mem c r′ → r′ ≤ r + ε)))
  ... | inj₁ yes = yes
  ... | inj₂ no = ⊥-elim (<-irrefl ≃-refl (<-≤-trans (bd rk mrk) final′))
    where
      b₀ : ℚᵘ
      b₀ = 0ℚᵘ + - 1ℚᵘ

      b₀<0 : b₀ < 0ℚᵘ
      b₀<0 = neg-diff 0<1

      step : ∀ r → mem c r → Σ ℚᵘ (λ r′ → mem c r′ × r + ε < r′)
      step r mr with lem (Σ ℚᵘ (λ r′ → mem c r′ × r + ε < r′))
      ... | inj₁ yes = yes
      ... | inj₂ none = ⊥-elim (no (r , mr , λ r′ m′ → help r′ m′ (≤-or-> r′ (r + ε))))
        where
          help : ∀ r′ → mem c r′ → r′ ≤ r + ε ⊎ r + ε < r′ → r′ ≤ r + ε
          help r′ m′ (inj₁ le) = le
          help r′ m′ (inj₂ lt) = ⊥-elim (none (r′ , m′ , lt))

      iter : ∀ n → Σ ℚᵘ (λ r → mem c r × b₀ + nat n * ε ≤ r)
      iter zero = b₀ , neg c b₀<0 ,
        ≤-≃ (≃-trans (+-cong (≃-refl {b₀}) (*-zeroˡ ε)) (+-identityʳ b₀))
      iter (suc n) with iter n
      ... | r , mr , h with step r mr
      ... | r′ , mr′ , lt = r′ , mr′ ,
        ≤-trans (≤-≃ (≃-trans (+-cong (≃-refl {b₀}) (nat-suc* n ε)) (ring₇ b₀ (nat n * ε) ε)))
          (<-≤ (≤-<-trans (+-mono-≤ h (≤-refl {ε})) lt))

      k = proj₁ (arch (M + 1ℚᵘ) 0<ε)
      hk = proj₂ (arch (M + 1ℚᵘ) 0<ε)

      rk = proj₁ (iter k)
      mrk = proj₁ (proj₂ (iter k))
      hrk = proj₂ (proj₂ (iter k))

      ringM : ∀ M → (0ℚᵘ + - 1ℚᵘ) + (M + 1ℚᵘ) ≃ M
      ringM = solve 1 (λ M → (con 0ℚᵘ :+ :- con 1ℚᵘ) :+ (M :+ con 1ℚᵘ) := M) ≃-refl

      final′ : M ≤ rk
      final′ = ≤-trans (≤-≃ (≃-sym (ringM M))) (≤-trans (+-mono-≤ (≤-refl {b₀}) hk) hrk)

  four : ℚᵘ
  four = (1ℚᵘ + 1ℚᵘ) + (1ℚᵘ + 1ℚᵘ)

  0<four : 0ℚᵘ < four
  0<four = ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< (≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<1 0<1)) (≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<1 0<1)))

  -- a rational scale `s` in `c`, nearly maximal, with `ρ = s + 2ε` outside `c` and `q ρ ≤ q′ s`
  pick : ∀ c {s₀ ρ₀ q q′} → 0ℚᵘ < s₀ → mem c s₀ → (∀ r → mem c r → r < ρ₀) → 0ℚᵘ ≤ q → q < q′ → q′ < 1ℚᵘ →
    Σ ℚᵘ λ s → Σ ℚᵘ λ ρ → (0ℚᵘ < s) × (0ℚᵘ < ρ) × (mem c ρ → ⊥) × mem c s × (q * ρ ≤ q′ * s)
  pick c {s₀} {ρ₀} {q} {q′} 0<s₀ ms₀ bd 0≤q q<q′ q′<1 with inv 0<four
  ... | t₄ , ht₄ = s , ρ , 0<s , 0<ρ , nmρ , ms , qρ≤q′s
    where
      δ = q′ + - q
      0<δ = pos-diff q<q′
      X = δ * s₀
      0<X = *-pos 0<δ 0<s₀
      0<t₄ = pos-of-inverse 0<four ht₄
      ε = X * t₄
      0<ε = *-pos 0<X 0<t₄
      h4 : (ε + ε) + (ε + ε) ≤ X
      h4 = ≤-≃ (≃-trans (solve 1 (λ e → (e :+ e) :+ (e :+ e) := e :* ((con 1ℚᵘ :+ con 1ℚᵘ) :+ (con 1ℚᵘ :+ con 1ℚᵘ))) ≃-refl ε)
                  (≃-trans (≃-trans (*-assoc X t₄ four) (*-cong (≃-refl {X}) ht₄)) (P.*-identityʳ X)))
      nsup = near-sup′ c ρ₀ bd 0<ε
      s = proj₁ nsup
      ms = proj₁ (proj₂ nsup)
      hs = proj₂ (proj₂ nsup)
      gp = gap {q} {q′} {s₀} {s} {ε} 0≤q q<q′ q′<1 0<s₀ 0<ε h4 (hs s₀ ms₀)
      0<s = proj₁ gp
      qρ≤q′s = proj₂ gp
      ρ = s + (ε + ε)
      0<εε : 0ℚᵘ < ε + ε
      0<εε = ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<ε 0<ε)
      0<ρ : 0ℚᵘ < ρ
      0<ρ = <-≤-trans 0<s (≤-trans (≤-≃ (≃-sym (+-identityʳ s))) (+-mono-≤ (≤-refl {s}) (<-≤ 0<εε)))
      nmρ : mem c ρ → ⊥
      nmρ mρ = <-irrefl ≃-refl (<-≤-trans (+-mono-≤-< (≤-refl {s}) (lt-add {ε} {ε} 0<ε)) (hs ρ mρ))

  -- from `s ∈ c`, `ρ ∉ c` and `q ρ ≤ q′ s` with q < q′ < 1: q = (q′/ρ)·s with 1/ρ ∈ c⁻¹
  assemble : ∀ c {q q′} → 0ℚᵘ ≤ q → q < q′ → q′ < 1ℚᵘ →
    (Σ ℚᵘ λ s → Σ ℚᵘ λ ρ → (0ℚᵘ < s) × (0ℚᵘ < ρ) × (mem c ρ → ⊥) × mem c s × (q * ρ ≤ q′ * s)) → mem (invC c ⊗ c) q
  assemble c {q} {q′} 0≤q q<q′ q′<1 (s , ρ , 0<s , 0<ρ , nmρ , ms , qρ≤q′s) with inv 0<ρ
  ... | t , ht = inj₂ (q′ * t , s , 0<r , 0<s , inj₂ (ρ , 0<ρ , nmρ , rρ<1) , ms , q≤rs)
    where
      0<q′ = ≤-<-trans 0≤q q<q′
      0<t = pos-of-inverse 0<ρ ht
      0<r : 0ℚᵘ < q′ * t
      0<r = *-pos 0<q′ 0<t
      rρ : (q′ * t) * ρ ≃ q′
      rρ = ≃-trans (*-assoc q′ t ρ) (≃-trans (*-cong (≃-refl {q′}) ht) (P.*-identityʳ q′))
      rρ<1 : (q′ * t) * ρ < 1ℚᵘ
      rρ<1 = ≃-<ˡ (≃-sym rρ) q′<1
      q≤rs : q ≤ (q′ * t) * s
      q≤rs = le-of-scaled {q} {q′ * t} {s} {ρ} {q′} 0<ρ rρ qρ≤q′s

  -- c⁻¹ · c ≥ 1 for a positive finite cut
  inv-mul-⊒ : ∀ c → Σ ℚᵘ (λ s₀ → 0ℚᵘ < s₀ × mem c s₀) → Σ ℚᵘ (λ ρ₀ → mem c ρ₀ → ⊥) → oneC ⊑ invC c ⊗ c
  inv-mul-⊒ c (s₀ , 0<s₀ , ms₀) (ρ₀ , nm₀) = mk⊑ go
    where
      bd : ∀ r → mem c r → r < ρ₀
      bd r mr with ≤-or-> ρ₀ r
      ... | inj₁ le = ⊥-elim (nm₀ (down c le mr))
      ... | inj₂ lt = lt

      go : ∀ q → q < 1ℚᵘ → mem (invC c ⊗ c) q
      go q q<1 with neg-or-nonneg q
      ... | inj₁ q<0 = inj₁ q<0
      ... | inj₂ 0≤q with dense q<1
      ... | q′ , q<q′ , q′<1 = assemble c 0≤q q<q′ q′<1 (pick c {s₀} {ρ₀} {q} {q′} 0<s₀ ms₀ bd 0≤q q<q′ q′<1)

  inv-mul : ∀ c → Σ ℚᵘ (λ s₀ → 0ℚᵘ < s₀ × mem c s₀) → Σ ℚᵘ (λ ρ₀ → mem c ρ₀ → ⊥) → invC c ⊗ c ≋ oneC
  inv-mul c hs hρ = inv-mul-⊑ c , inv-mul-⊒ c hs hρ
