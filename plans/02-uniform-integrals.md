# Plan 2: moments and unbiased estimation for the uniform distribution

## Goal
Prove, in the library, for X₁,…,Xₙ iid uniform on [0,1] (then [a,b]):
`E[x̄] = μ`, `Var(x̄) = σ²/n`, and `E[s²] = σ²` with `s² = Σ(Xᵢ − x̄)²/(n−1)`. Exact values: `μ = ½`, `σ² = 1/12`.
The generic theorem (any family with mean μ and variance σ²) should come out as a by-product.
This is the stepping stone to Gaussian estimation, Plan 3, and avoids exp/π.

## Starting point
Available: `Continuous/Uniform` (`uniform`), `UniformMean` (E[u] = ½), `UniformCDF`, the fair-coin product/independence
(`CoinIndep`, `Interleave`), the integral `J`/`Lebesgue` with Tonelli, Fubini, `FunInf`.
Missing: signed values, subtraction, E[X²], n-fold products, linearity for signed functions.

## Status (2026-10-30)
- **Step 1 (signed layer) DONE** in `Analysis/Signed`, `SignedOmega`, `SignedIntegral`: the signed values are the Grothendieck ring over the *bounded* elements (restriction to finite elements is essential: with `∞` the construction collapses), which needs no cancellation, no classical principle and no Dedekind reals. `E` has additivity, negation, scaling by signed constants, and `E` of a constant. Not yet: monotonicity of `E`, products of signed functions.
- **Step 2 (second moment) partly DONE** in `Continuous/UniformMoment`: `second-moment : m + m + m ≈ 1` for `m = E[u²]` (stated without division). Proof: `e²` is a `Fun` (`Meas→Fun`), the first-bit decomposition `firstBit-fun` with `e(true::s)=½+½e(s)`, `e(false::s)=½e(s)` and the mean give `4m = 1 + m`, then cancellation (`m ≤ 1`). The solver must run over an abstract semiring (`module Alg`), since on the concrete cut semiring it takes minutes. `Var u = 1/12` is DONE too: `Analysis/Variance` has products of bounded signed functions (`_*SF_[_]`), `Var f = E[(f−μ)²]` and `var-formula : Var f ≃ E[f²] − (E f)²`; `Continuous/UniformVariance` proves `variance : x12 (Var u) ≃ 1S` (twelve copies add up to one; the pure algebra is `Arith.var-arith`). Lessons: keep `Var` and `var-formula` `abstract`, and state lemmas over abstract variables, otherwise conversion unfolds signed records for minutes. Remaining in step 2: the restatement `∫ uniform id ≈ half`.
- **Steps 3 and 4 DONE (2026-10-30)**, all division-free (the signed ring has no inverses of naturals):
  `Analysis/Estimator` (generic: `E Sₙ = nμ`, `E Sₙ² = nσ² + n²μ²`, `E (nQₙ − Sₙ²) = n(n−1)σ²` over an abstract ring `R` with additive `E`),
  `Analysis/BoundedRing` (the ring of bounded signed functions on a probability space; equality is pointwise equality of `Sg` values, the ring structure comes from `Algebra.Morphism.RingMonomorphism`) with `Analysis/BoundedCancel` (cancel bounded elements),
  `Continuous/CoinCoords` (coordinates of the coin: `J-coord`, `J-split`, `J-indep`, signed `E-indep`),
  `Continuous/UniformSample` (the uniform instance: `sample-mean-unbiased`, `sample-mean-variance`, `sample-variance`).
  Compile times: each module 3–12 s. Lessons: state lemmas over abstract variables, give implicit arguments of `Meas`-indexed lemmas explicitly (`Meas` is not injective), name intermediate `Sg` expressions (`VarS`, `ESS`) instead of repeating them in a type that is unified, and annotate implicit `Sg` arguments (`∀ {a b : Sg}`): unresolved ones make Agda unfold the cut semiring.
- **Step 5 DONE**: `Estimator.Affine` (moments of `a + c·Xᵢ`, from `E (κ s) = s` and `E (κ s · x) = s · E x`; `BoundedRing.κB`) and `Continuous/UniformInterval`. Only the restatement `∫ uniform id ≈ half` remains.

## Steps

1. **Signed layer (`Analysis/Signed.agda`).** Define signed values as pairs `(p, n)` of `[0,∞]` with the usual
   quotient (or a setoid), with `+`, `−`, `×`, `≤`. Restrict to finite values where possible.
   Integrable signed function: `h⁺, h⁻` both with finite integral. `E h = ∫h⁺ − ∫h⁻`.
   Prove linearity (`E(f+g) = E f + E g`, `E(c·f) = c·E f`), monotonicity, and `E` of constants.
   This reuses `Analysis/Unbounded` and `Lebesgue`. Decision made: a Grothendieck construction over the elements bounded by a natural number (see Status), not Dedekind reals.
   Also decide the carrier for the variance: it is nonnegative, so `[0,∞]`-valued with a signed difference
   inside is enough.

2. **Moments of the uniform distribution.** `E[u] = ½` exists. Add `E[u²] = ⅓`, hence `Var u = 1/12`.
   Route: reuse the self-similarity lemma (`Analysis/SelfSimilar`) with the first-bit decomposition that gave
   the CDF and the mean. For u² the first-bit step gives `E[u²] = ¼·E[u²] + ¼·E[u] + ¼·(1/2)·…`; solve the
   linear equation. This needs division by a finite positive number: `Analysis/LowerInverse` provides it (classical).
   Alternative if that is painful: `E[(u − ½)²] = 1/12` directly.

3. **n-fold products and iid samples.** Build `Xs : 𝕀 ^ n` from the fair coin via `Interleave`, or the abstract
   `Tensor` product, and prove the marginals are `uniform` and the coordinates independent.
   Statement: `∫ (f₁(x₁)·…·fₙ(xₙ)) = ∏ ∫ fᵢ`. Induct on n using `fairCoin-indep`; this is the main assembly work,
   so check first what `Interleave` already gives for more than two components.

4. **Estimator theorem (generic).** Hypotheses: a family `Xᵢ` of integrable random variables, pairwise independent,
   with `E Xᵢ = μ` and `Var Xᵢ = σ²`. Prove:
   - `E[x̄] = μ` (linearity only; no independence needed)
   - `Var(x̄) = σ²/n` (uses `E[XᵢXⱼ] = μ²` for i ≠ j)
   - `E[s²] = σ²` (algebra: `Σ(Xᵢ − x̄)² = ΣXᵢ² − n·x̄²`, then the two facts above).
   The algebra needs a commutative ring or field of signed values with finite sums. Check what the signed
   layer offers; a small `Algebra` instance may be needed to use the standard library's solver.

5. **Instantiate.** Apply Step 4 to `uniform`, then to the scaled version `a + (b−a)u` (affine map of a random variable,
   `E` linear, `Var` quadratic scaling). Statement for the sample mean and variance as a `Calculation`, in the
   style of `Example/Probability.agda`.

6. **Documentation.** Add a `README` section and a `docs/Guide.md` example "estimating μ and σ²"
   (ties into Plan 1).

## Effort (rough, uncertain)
Step 1: about 1–2 weeks (the quotient algebra and linearity proofs are tedious and prone to the compile-time
problems already noted in TODO). Step 2: days. Step 3: about a week (depends on what exists). Step 4: about a week.
Step 5: days.

## Done when
`make check` passes with the three theorems stated for the uniform distribution, with `lem` and `funext` the only
hypotheses, listed in `Docs/Classical.md`.

## Risks
- Compile time: previous work hit 70-minute and 400-second blowups from unfolded lower cuts. Keep statements generic
  in an abstract algebra and bridge at the end, as `Example/Probability.agda` does.
- Pairwise independence of n coordinates from the binary `fairCoin-indep` may need a new lemma on infinite
  interleaving. If it is large, restrict to n = 2, 3 first as a sanity check.
- `1/(n−1)` and `σ²/n` need inverses of naturals in the value semiring; those are finite and positive, so
  `LowerInverse` should apply. Confirm.
