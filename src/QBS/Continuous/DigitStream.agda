{-# OPTIONS --safe --without-K #-}

-- The digit stream of a point of `[0,∞]` (plan 03, "Uniqueness on the half-line"; the engine of `Continuous/DigitCode`).
-- The code is the output of a small machine whose state is either `un j` (j ones emitted, still in the unary integer part)
-- or `fr d m` (in the binary part: the point lies in the dyadic interval [m/2ᵈ, (m+1)/2ᵈ)).  In state s the machine asks
-- "is the threshold `thr s` ≤ x?" (decided by excluded middle), emits the answer, and moves to `sB s answer`.
--   * `out x s` is the emitted stream and `digits x = out x (un 0)`; `digits-cong`: equal points have equal digits;
--   * `borel-out`: each bit is a Boolean combination of the Borel sets `{r | thr s ≤ h r}` (`Intervals.ge-borel`), by
--     induction on the position; this is `meas-digits`;
--   * the invariants: `Tgt n M x` says x ∈ [M/2ⁿ, (M+1)/2ⁿ).  `un-run`/`blk-ge` (unary part: the block of `digits x` is
--     the integer part of x), `fr-match` (binary part: a word is a prefix iff x is in the dyadic interval), `fr-inv`.
module QBS.Continuous.DigitStream where

open import Level using (lift)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; s≤s; z≤n)
import Data.Nat.Properties as ℕ
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; _:=_; con)
open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Sum.Base as Sum
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import QBS.Classical using (LEM₀)
open import QBS.Borel.Core using (Cantor; Borel; compl; resp; union₂; inter₂; _≐_)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cells using (Word; Match; Blk; Ones; Cell; Top; dropC)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (_⊑_; mk⊑; ⊑-trans)
open _⊑_ using (ap)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.DyadicAlg using (module AlgDy)
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Continuous.Intervals using (module Intervals)

-- the binary value of a word, most significant bit first
val : Word → ℕ
val [] = zero
val (b ∷ w) = (if b then 2 ^ length w else zero) + val w

-- arithmetic of values
val-lt : ∀ w → val w < 2 ^ length w
val-lt [] = s≤s z≤n
val-lt (true ∷ w) = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.+-suc (2 ^ length w) (val w))))
  (ℕ.≤-trans (ℕ.+-monoʳ-≤ (2 ^ length w) (val-lt w)) (ℕ.≤-reflexive (cong (2 ^ length w +_) (sym (ℕ.+-identityʳ _)))))
val-lt (false ∷ w) = ℕ.<-≤-trans (val-lt w) (ℕ.m≤m+n _ _)

module DigitStream (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_) renaming (Carrier to ∣A∣)
  open Meas lem using (Meas)
  open Intervals lem using (Ge; ge-borel; dy)
  open Exp A using (natE)
  open Arch (lowerRealsArch lem) using (half) renaming (half+half to hh)
  open AlgDy A half hh using (dbl; ix)
  open AlgDigit A half hh using (dbl-*2; dy-dbl; dy-le; dy-ge; dy-mono; natE-mono; mN)
  open OmegaSemiring A using (≤-trans; ≤-reflexive; *-identityʳ)

  ----------------------------------------------------------------------------
  -- deciding a proposition

  dB : Set → Bool
  dB P = Sum.[ (λ _ → true) , (λ _ → false) ]′ (lem P)

  dB-yes : ∀ {P} → P → dB P ≡ true
  dB-yes {P} p with lem P
  ... | inj₁ _ = refl
  ... | inj₂ np = ⊥-elim (np p)

  dB-no : ∀ {P} → (P → ⊥) → dB P ≡ false
  dB-no {P} np with lem P
  ... | inj₁ p = ⊥-elim (np p)
  ... | inj₂ _ = refl

  dB-true : ∀ {P} → dB P ≡ true → P
  dB-true {P} e with lem P
  ... | inj₁ p = p

  dB-false : ∀ {P} → dB P ≡ false → P → ⊥
  dB-false {P} e p = bad (trans (sym (dB-yes p)) e)
    where bad : true ≡ false → ⊥
          bad ()

  dB-cong : ∀ {P Q} → (P → Q) → (Q → P) → dB P ≡ dB Q
  dB-cong {P} {Q} f g with lem P
  ... | inj₁ p = sym (dB-yes (f p))
  ... | inj₂ np = sym (dB-no (λ q → np (g q)))

  ----------------------------------------------------------------------------
  -- the machine

  data St : Set where
    un : ℕ → St
    fr : ℕ → ℕ → St

  -- the threshold asked about in a state, and the next state
  thr : St → ∣A∣
  thr (un j) = natE (suc j)
  thr (fr d m) = dy (suc d) (suc (dbl m))

  sB : St → Bool → St
  sB (un j) true = un (suc j)
  sB (un j) false = fr zero j
  sB (fr d m) b = fr (suc d) (ix b m)

  bit : ∣A∣ → St → Bool
  bit x s = dB (Ge (thr s) x)

  out : ∣A∣ → St → Cantor
  out x s zero = bit x s
  out x s (suc i) = out x (sB s (bit x s)) i

  digits : ∣A∣ → Cantor
  digits x = out x (un zero)

  -- equal points have equal digits
  out-cong : ∀ {x y} → x ≈ y → ∀ i s → out x s i ≡ out y s i
  out-cong e zero s = dB-cong (λ g q m → ap (proj₁ e) q (g q m)) (λ g q m → ap (proj₂ e) q (g q m))
  out-cong {x} {y} e (suc i) s = trans (cong (λ b → out x (sB s b) i) bx) (out-cong e i (sB s (bit y s)))
    where bx : bit x s ≡ bit y s
          bx = dB-cong (λ g q m → ap (proj₁ e) q (g q m)) (λ g q m → ap (proj₂ e) q (g q m))

  digits-cong : ∀ {x y} → x ≈ y → ∀ i → digits x i ≡ digits y i
  digits-cong e i = out-cong e i (un zero)

  ----------------------------------------------------------------------------
  -- measurability

  borel-bit : ∀ {h : R₁ → ∣A∣} → Meas h → ∀ s b → Borel (λ c → bit (h (lift c)) s ≡ b)
  borel-bit {h} mh s true = resp (λ c → dB-yes , dB-true) (ge-borel (thr s) mh)
  borel-bit {h} mh s false = resp (λ c → dB-no , (λ e g → dB-false e g)) (compl (ge-borel (thr s) mh))

  borel-out : ∀ {h : R₁ → ∣A∣} → Meas h → ∀ i s b → Borel (λ c → out (h (lift c)) s i ≡ b)
  borel-out mh zero s b = borel-bit mh s b
  borel-out {h} mh (suc i) s b =
    resp e (union₂ (inter₂ G (borel-out mh i (sB s true) b))
                   (inter₂ (compl G) (borel-out mh i (sB s false) b)))
    where
      G = ge-borel (thr s) mh
      e : ∀ c → _
      e c = fwd , bwd
        where
          x = h (lift c)
          fwd : _ → out x s (suc i) ≡ b
          fwd (inj₁ (g , o)) = subst (λ t → out x (sB s t) i ≡ b) (sym (dB-yes g)) o
          fwd (inj₂ (ng , o)) = subst (λ t → out x (sB s t) i ≡ b) (sym (dB-no ng)) o
          bwd : out x s (suc i) ≡ b → _
          bwd o = Sum.[ (λ g → inj₁ (g , subst (λ t → out x (sB s t) i ≡ b) (dB-yes g) o))
                      , (λ ng → inj₂ (ng , subst (λ t → out x (sB s t) i ≡ b) (dB-no ng) o))
                      ]′ (lem (Ge (thr s) x))

  meas-digits : ∀ {h : R₁ → ∣A∣} → Meas h → ∀ i b → Borel (λ c → digits (h (lift c)) i ≡ b)
  meas-digits mh i b = borel-out mh i (un zero) b

  ----------------------------------------------------------------------------
  -- the invariant: x lies in the dyadic interval [M/2ⁿ, (M+1)/2ⁿ)

  Tgt : ℕ → ℕ → ∣A∣ → Set
  Tgt n M x = Ge (dy n M) x × (Ge (dy n (suc M)) x → ⊥)

  ≈⊑ : ∀ {a b : ∣A∣} → a ≈ b → a ⊑ b
  ≈⊑ = proj₁

  ≈⊒ : ∀ {a b : ∣A∣} → a ≈ b → b ⊑ a
  ≈⊒ = proj₂

  Ge-⊑ : ∀ {a b x} → a ⊑ b → Ge b x → Ge a x
  Ge-⊑ le g q m = g q (ap le q m)

  Tgt-≡ : ∀ {n n′ M M′ x} → n ≡ n′ → M ≡ M′ → Tgt n M x → Tgt n′ M′ x
  Tgt-≡ refl refl t = t

  -- one step of the machine: the interval of x halves according to the bit
  fr-down : ∀ x d m b → Tgt d m x → bit x (fr d m) ≡ b → Tgt (suc d) (ix b m) x
  fr-down x d m true (g , ng) e = dB-true e , λ gC → ng (Ge-⊑ {x = x} (≈⊒ (dy-dbl (suc m) d)) gC)
  fr-down x d m false (g , ng) e = Ge-⊑ {x = x} (≈⊑ (dy-dbl m d)) g , dB-false e

  fr-up : ∀ x d m b → Tgt (suc d) (ix b m) x → Tgt d m x × (bit x (fr d m) ≡ b)
  fr-up x d m true (gB , nC) = (Ge-⊑ {x = x} (⊑-trans (≈⊒ (dy-dbl m d)) (dy-mono (suc d) (ℕ.n≤1+n _))) gB
    , λ g → nC (Ge-⊑ {x = x} (≈⊑ (dy-dbl (suc m) d)) g)) , dB-yes gB
  fr-up x d m false (gA , nB) = (Ge-⊑ {x = x} (≈⊒ (dy-dbl m d)) gA
    , λ g → nB (Ge-⊑ {x = x} (⊑-trans (dy-mono (suc d) (ℕ.n≤1+n _)) (≈⊑ (dy-dbl (suc m) d))) g)) , dB-no nB

  ----------------------------------------------------------------------------
  -- the binary part: a word is a prefix of the stream iff x lies in the corresponding dyadic interval

  -- `dbl m · p = m · (2 · p)`
  dbl-mul : ∀ m p → dbl m * p ≡ m * (2 * p)
  dbl-mul m p = trans (cong (_* p) (dbl-*2 m)) (solve 2 (λ m p → m :* con 2 :* p := m :* (con 2 :* p)) refl m p)

  val-ix : ∀ b m l v → m * 2 ^ suc l + ((if b then 2 ^ l else zero) + v) ≡ ix b m * 2 ^ l + v
  val-ix true m l v = trans (solve 3 (λ m p v → m :* (con 2 :* p) :+ (p :+ v) := (p :+ m :* (con 2 :* p)) :+ v) refl m (2 ^ l) v)
    (cong (λ t → (2 ^ l + t) + v) (sym (dbl-mul m (2 ^ l))))
  val-ix false m l v = cong (_+ v) (sym (dbl-mul m (2 ^ l)))

  suc-le : ∀ k p v → suc v ≤ p → suc (k * p + v) ≤ suc k * p
  suc-le k p v lt =
    ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.+-suc _ v)))
      (ℕ.≤-trans (ℕ.+-monoʳ-≤ (k * p) lt) (ℕ.≤-reflexive (ℕ.+-comm _ _)))

  -- the bit of the stream is read off from the final interval
  bit-of : ∀ x b d m l v → suc v ≤ 2 ^ l → Tgt (l + suc d) (ix b m * 2 ^ l + v) x → bit x (fr d m) ≡ b
  bit-of x true d m l v lt (g , ng) = dB-yes (Ge-⊑ {x = x} (dy-le l (suc d) (suc (dbl m)) _ (ℕ.m≤m+n _ v)) g)
  bit-of x false d m l v lt (g , ng) = dB-no (λ gB → ng (Ge-⊑ {x = x} (dy-ge l (suc d) (suc (dbl m)) _ le) gB))
    where le : suc (dbl m * 2 ^ l + v) ≤ suc (dbl m) * 2 ^ l
          le = suc-le (dbl m) (2 ^ l) v lt

  FrMatch : ∀ x w d m → Set
  FrMatch x w d m =
    (Match w (out x (fr d m)) → Tgt (length w + d) (m * 2 ^ length w + val w) x)
    × (Tgt (length w + d) (m * 2 ^ length w + val w) x → Match w (out x (fr d m)))

  -- one step of `fr-match`, given the result for the tail
  fr-cons : ∀ x b w d m → (bit x (fr d m) ≡ b → FrMatch x w (suc d) (ix b m)) → FrMatch x (b ∷ w) d m
  fr-cons x b w d m rec = fwd , bwd
    where
      l = length w
      fwd : Match (b ∷ w) (out x (fr d m)) → _
      fwd (eb , mt) = Tgt-≡ (ℕ.+-suc l d) (sym (val-ix b m l (val w)))
        (proj₁ (rec eb) (subst (λ t → Match w (out x (fr (suc d) (ix t m)))) eb mt))
      bwd : Tgt (suc l + d) _ x → Match (b ∷ w) (out x (fr d m))
      bwd t = eb , subst (λ t → Match w (out x (fr (suc d) (ix t m)))) (sym eb) (proj₂ (rec eb) t′)
        where
          t′ : Tgt (l + suc d) (ix b m * 2 ^ l + val w) x
          t′ = Tgt-≡ (sym (ℕ.+-suc l d)) (val-ix b m l (val w)) t
          eb : bit x (fr d m) ≡ b
          eb = bit-of x b d m l (val w) (val-lt w) t′

  fr-match : ∀ x w d m → Tgt d m x → FrMatch x w d m
  fr-match x [] d m T = (λ _ → Tgt-≡ refl (sym e) T) , (λ _ → tt)
    where e : m * 1 + 0 ≡ m
          e = trans (ℕ.+-identityʳ _) (ℕ.*-identityʳ m)
  fr-match x (b ∷ w) d m T =
    fr-cons x b w d m (λ eb → fr-match x w (suc d) (ix b m) (fr-down x d m b T eb))

  ----------------------------------------------------------------------------
  -- the unary part: the block of `digits x` is the integer part of x

  -- the machine in state `un j` (with x ≥ j) and x ∈ [J, J+1), J = j + k: k ones, a zero, then the binary part from J
  un-run : ∀ x k j J → J ≡ j + k → Ge (natE j) x → Ge (natE J) x → (Ge (natE (suc J)) x → ⊥) →
    Blk k (out x (un j)) × (∀ i → out x (un j) (suc k + i) ≡ out x (fr zero J) i)
  un-run x zero j J pj gj gJ nJ = go (trans pj (ℕ.+-identityʳ j)) nJ
    where
      go : J ≡ j → (Ge (natE (suc J)) x → ⊥) → _
      go refl n = (tt , dB-no n) , λ i → subst (λ t → out x (sB (un j) t) i ≡ out x (fr zero j) i) (sym (dB-no n)) refl
  un-run x (suc k) j J pj gj gJ nJ = ((bt , proj₁ b′) , proj₂ b′)
    , λ i → subst (λ t → out x (sB (un j) t) (suc k + i) ≡ out x (fr zero J) i) (sym bt) (proj₂ ih i)
    where
      pJ : J ≡ suc (j + k)
      pJ = trans pj (ℕ.+-suc j k)
      g1 : Ge (natE (suc j)) x
      g1 = Ge-⊑ {x = x} (natE-mono (subst (suc j ≤_) (sym pJ) (s≤s (ℕ.m≤m+n j k)))) gJ
      bt : bit x (un j) ≡ true
      bt = dB-yes g1
      ih = un-run x k (suc j) J pJ g1 gJ nJ
      b′ = subst (λ t → Ones k (out x (sB (un j) t)) × (out x (sB (un j) t) k ≡ false)) (sym bt) (proj₁ ih)

  -- conversely, a block of ones forces x into [J, J+1)
  blk-ge : ∀ x k j J → J ≡ j + k → Ge (natE j) x → Blk k (out x (un j)) → Ge (natE J) x × (Ge (natE (suc J)) x → ⊥)
  blk-ge x zero j J pj gj (_ , y0) = go (trans pj (ℕ.+-identityʳ j))
    where
      go : J ≡ j → _
      go refl = gj , dB-false y0
  blk-ge x (suc k) j J pj gj ((y0 , ones) , yk) = blk-ge x k (suc j) J (trans pj (ℕ.+-suc j k)) (dB-true y0)
    (subst (λ t → Ones k (out x (sB (un j) t)) × (out x (sB (un j) t) k ≡ false)) y0 (ones , yk))

  ge0 : ∀ x → Ge (natE zero) x
  ge0 x = ap (OmegaSemiring.0-least A {x})

  -- a point that is not infinite has an integer part
  floor-ex : ∀ x → ((∀ k → Ge (natE k) x) → ⊥)
           → Σ ℕ (λ k → Ge (natE k) x × (Ge (natE (suc k)) x → ⊥))
  floor-ex x ntop =
    Sum.[ (λ s → s) , (λ none → ⊥-elim (ntop (all none))) ]′
      (lem (Σ ℕ (λ k → Ge (natE k) x × (Ge (natE (suc k)) x → ⊥))))
    where
      all : (Σ ℕ (λ k → Ge (natE k) x × (Ge (natE (suc k)) x → ⊥)) → ⊥)
          → ∀ k → Ge (natE k) x
      all none zero = ge0 x
      all none (suc k) = Sum.[ (λ g → g) , (λ ng → ⊥-elim (none (k , all none k , ng))) ]′ (lem (Ge (natE (suc k)) x))

  -- an infinite point has the all-true code, and conversely
  top-un : ∀ x → (∀ k → Ge (natE k) x) → ∀ j i → out x (un j) i ≡ true
  top-un x top j zero = dB-yes (top (suc j))
  top-un x top j (suc i) = subst (λ t → out x (sB (un j) t) i ≡ true) (sym (dB-yes (top (suc j)))) (top-un x top (suc j) i)

  top-inf : ∀ x → (∀ i → digits x i ≡ true) → ∀ k → Ge (natE k) x
  top-inf x top zero = ge0 x
  top-inf x top (suc k) = Sum.[ (λ g → g) , (λ ng → ⊥-elim (bad (trans (sym (yk ng)) (top k)))) ]′ (lem (Ge (natE (suc k)) x))
    where
      gk = top-inf x top k
      yk : (Ge (natE (suc k)) x → ⊥) → digits x k ≡ false
      yk ng = proj₂ (proj₁ (un-run x k zero k refl (ge0 x) gk ng))
      bad : false ≡ true → ⊥
      bad ()

  ----------------------------------------------------------------------------
  -- the binary part: the intervals of the successive states

  fr-inv : ∀ x N d m n → n ≡ N + d → Tgt d m x → Tgt n (mN (out x (fr d m)) m N) x
  fr-inv x zero d m n refl T = T
  fr-inv x (suc N) d m n refl T =
    Tgt-≡ (ℕ.+-suc N d) refl
      (fr-inv x N (suc d) (ix (bit x (fr d m)) m) (N + suc d) refl (fr-down x d m _ T refl))

  ----------------------------------------------------------------------------
  -- cells are dyadic intervals, the all-true point is ∞

  -- the integer part of a point of [M/2ⁿ, (M+1)/2ⁿ) with a·2ⁿ ≤ M < (a+1)·2ⁿ is a
  tgt-floor : ∀ x n a M → a * 2 ^ n ≤ M → suc M ≤ suc a * 2 ^ n → Tgt n M x → Ge (natE a) x × (Ge (natE (suc a)) x → ⊥)
  tgt-floor x n a M lo hi t = (λ q m → proj₁ t′ q (ap lo′ q m)) , (λ g → proj₂ t′ (λ q m → g q (ap hi′ q m)))
    where
      t′ = Tgt-≡ (sym (ℕ.+-identityʳ n)) refl t
      lo′ = ≤-trans (≤-reflexive (OmegaSemiring.sym A (*-identityʳ (natE a)))) (dy-le n zero a M lo)
      hi′ = ≤-trans (dy-ge n zero (suc a) (suc M) hi) (≤-reflexive (*-identityʳ (natE (suc a))))

  fl-tgt : ∀ x k → Ge (natE k) x → (Ge (natE (suc k)) x → ⊥) → Tgt zero k x
  fl-tgt x k gk ng = (λ q m → gk q (ap (≤-reflexive (*-identityʳ (natE k))) q m))
    , (λ g → ng (λ q m → g q (ap (≤-reflexive (OmegaSemiring.sym A (*-identityʳ (natE (suc k))))) q m)))

  match-≗ : ∀ w {c d : Cantor} → (∀ i → c i ≡ d i) → Match w c → Match w d
  match-≗ [] e _ = tt
  match-≗ (b ∷ w) e (p , q) = trans (sym (e zero)) p , match-≗ w (λ i → e (suc i)) q

  -- the unary part of the machine, run on the integer part k
  unRun : ∀ x {k} → Ge (natE k) x → (Ge (natE (suc k)) x → ⊥) →
    Blk k (out x (un zero)) × (∀ i → out x (un zero) (suc k + i) ≡ out x (fr zero k) i)
  unRun x {k} gk ng = un-run x k zero k refl (ge0 x) gk ng

  cell-fwd : ∀ x k w → Cell k w (digits x) → Tgt (length w) (k * 2 ^ length w + val w) x
  cell-fwd x k w (blk , mt) =
    Tgt-≡ (ℕ.+-identityʳ _) refl
      (proj₁ (fr-match x w zero k T0) (match-≗ w (proj₂ (unRun x gk ng)) mt))
    where gk = proj₁ (blk-ge x k zero k refl (ge0 x) blk)
          ng = proj₂ (blk-ge x k zero k refl (ge0 x) blk)
          T0 = fl-tgt x k gk ng

  cell-bwd : ∀ x k w → Tgt (length w) (k * 2 ^ length w + val w) x → Cell k w (digits x)
  cell-bwd x k w t = proj₁ (unRun x gk ng) , match-≗ w (λ i → sym (proj₂ (unRun x gk ng) i))
    (proj₂ (fr-match x w zero k (fl-tgt x k gk ng)) (Tgt-≡ (sym (ℕ.+-identityʳ _)) refl t))
    where fl = tgt-floor x (length w) k _ (ℕ.m≤m+n _ _)
                         (suc-le k (2 ^ length w) (val w) (val-lt w)) t
          gk = proj₁ fl
          ng = proj₂ fl

  cell-iff : ∀ x k w →
    (Cell k w (digits x) → Tgt (length w) (k * 2 ^ length w + val w) x)
    × (Tgt (length w) (k * 2 ^ length w + val w) x → Cell k w (digits x))
  cell-iff x k w = cell-fwd x k w , cell-bwd x k w

  top-iff : ∀ x → (Top (digits x) → ∀ k → Ge (natE k) x) × ((∀ k → Ge (natE k) x) → Top (digits x))
  top-iff x = top-inf x , (λ top i → top-un x top zero i)
