# Plan 07: exponential families, sufficiency, PAIRS, and density approximation (proposed 2026-11-05; rewritten 2026-11-05)

Goal: the theory of **exponential families** (product factorisation, conjugate updating, Bayesian sufficiency), their
**information geometry** (KL as a Bregman divergence, convexity of the log-partition, the Pythagorean identity and
moment matching), the algebraic engine of the **PAIRS theorem** (sufficiency on pairs extrapolates to every set size,
through Cauchy's functional equation), and as much of **Barron–Sheu density approximation** as the library can
support.  Item numbers continue plan 05 (last: 55).  Each phase is skeletoned first (holes, statements, headers),
then filled by agents, two at a time, as in plans 03 and 05.  Ideas that are currently out of reach are kept in
"Out of reach", each with the reason, so that they can be picked up when the missing pieces exist.

## Literature

1. **Antoine Wehenkel, Michael Kagan, Lukas Heinrich, and Chris Pollard (2026)**, *It Just Takes Two: Scaling
   Amortized Inference to Large Sets*, arXiv:2605.07972 [cs.LG].  In `lit/wehenkel2026pairs.pdf` (source in
   `lit/wehenkel2026pairs_src/`, text in `lit/wehenkel2026pairs.txt`).
2. **Andrew R. Barron and Chyong-Hwa Sheu (1991)**, *Approximation of Density Functions by Sequences of Exponential
   Families*, The Annals of Statistics 19(3):1347–1369, DOI 10.1214/aos/1176348252.  Summary and notes in
   `lit/barron_sheu1991.md`.

### Synthesis

In amortized Bayesian inference (for example neural posterior estimation), observation sets X_N = {x₁, …, x_N} share
latent parameters θ (and nuisance factors ψ).  Deep Set architectures aggregate by permutation-invariant mean pooling,
M_t(X_N) = (1/N) Σᵢ t(xᵢ).  Exponential families explain why this works, through two mechanisms:

```
     Arbitrary smooth likelihood / prior p(X | θ)
                         │
                         │  Barron & Sheu (1991)
                         │  exponential family sieve: D_KL(f ‖ f_k) ≤ O(k^{−2r})
                         ▼
     k-dimensional exponential family
     p(x | θ) = h(x) exp(⟨η(θ), T(x)⟩ − A(θ))
                         │
                         │  Fisher–Neyman factorisation:
                         │  p(X_N | θ) factorises through (1/N) Σᵢ T(xᵢ)
                         ▼
     Mean-pool representation learning: PAIRS (Wehenkel et al. 2026)
     • Cauchy functional equation on pairs {1, 2} forces t*(x) = A t_ω(x) + b
     • training on N ∈ {1, 2} guarantees sufficiency for all N ≥ 1
```

* **PAIRS.**
  1. *Theorem 1 (pairs extrapolate to every N).*  Under mild regularity, if an embedder t_ω is sufficient for θ at
     N = 1 (t* = g ∘ t_ω) and its mean pool is sufficient at N = 2, the aggregation map satisfies
     g(y₁) + g(y₂) = h̃(y₁ + y₂), hence g(y) = A y + b, and (M_{t_ω}(X_N), N) is sufficient at every N ≥ 1.
  2. *Corollary 2 (characterisation).*  By Koopman–Pitman–Darmois, a fixed finite-dimensional mean-pool sufficient
     statistic at every N ≥ 1 exists if and only if the likelihood is an exponential family with canonical
     statistic t*.
  3. *Corollary 3 (cardinality invariance).*  Training on {1, M} for any M ≥ 2 recovers the same affine class.
* **Barron & Sheu.**  Sequences of exponential families f_k(x; θ) = exp(Σ_{j≤k} θⱼ φⱼ(x) − ψ_k(θ)) with polynomial,
  trigonometric or spline bases approximate any density whose log-density is in the Sobolev space Hʳ, with KL error
  O(k^{−2r}); a larger embedding dimension lets the mean pool approximate complex posteriors.

**What this plan formalises of the above.**  The exponential-family side (factorisation through Σ T, conjugate
updating, Bayesian sufficiency) in full; the information geometry without derivatives; the algebra of Theorem 1 and
Corollary 3, with sufficiency at N = 1 and N = 2 taken in factorised form, plus the affine conclusion under a
regularity hypothesis.  Corollary 2, the general measure-theoretic notion of sufficiency, and the Barron–Sheu rate are
out of reach (see the last section).

## What exists

- Discrete Bayesian updating (`Inference/Bayesian`): `sequential`, `evidence-sequential`, `predictive-chain`; the
  Bernoulli model `likSeq-counts : likSeq xs θ ≈ p^(successes xs) · q^(failures xs)`, a one-parameter discrete
  exponential family in multiplicative form.
- Sample statistics (`Analysis/Estimator`, `Inference/Frequentist`): term algebra (`sumT`, `sqT`) evaluated in any
  commutative ring with the ring solver; unbiased sample mean and variance.  Affine identities `Analysis/AffineAlg`.
- Plan 05: finite products `FinProd` (`ΠQ`, `prodⁿ`, `∫-rectⁿ`), `FinProdProb.prodPⁿ`, `IID`, `CondIID` (kernel
  powers, the Bayesian joint and marginal), vectors and matrices `Analysis/SgLinAlg`, random vectors
  `RandomVector`, push-forward laws `RandomVectorLaw`, sums over `Fin` (`SgMoments.sumT`).
- Exponential and logarithm: `Analysis/Exp` (`exp` on an ω-semiring), `Analysis/NegExp` (e^{−x} on the lower reals),
  `Continuous/SignedLog` (`logS x : Sg` for 0 < x < ∞ with `log-mul`, `log-one`, `log-exp`), `Continuous/LogCore`.
- Densities and information: `SFiniteReweight.reweightPre`, `Entropy.densPre` and `∫-dens`, `logT`; `KLDiv`
  (`KL Q p i = E_{pQ}[log p]`, i.e. D(pQ ‖ Q); `KL-nonneg`, `KL-cong`, `KL-one`); `InfoProduct` (`KL-⊗`, `Ent-⊗`).
- Distributions: Exp(λ) (`Continuous/ExpDist`, `Inference/ExpRateDist`, moments n!/λⁿ⁺¹), N(μ, σ²)
  (`Inference/GaussReal`, `GaussVar`), N(0, Iₙ) and N(b, AAᵀ) (`GaussVector`, `GaussVectorLaw`), Beta–Binomial
  (`Continuous/BetaIntegral`, `Inference/CoinPosterior`); normalisation without division by a normaliser n with
  Z · n ≈ 1 (`RealDensity.Sym`).
- Archimedean structure of the lower reals (`Analysis/Archimedean`: halves, Archimedean closure, cancellation).
- Not present: a general notion of sufficiency, conditional distributions given a statistic (disintegration),
  derivatives of parameter integrals in general, Sobolev spaces, approximation theory.

## Decisions (proposed)

- **Values.**  Statistics and natural parameters are vectors over the signed values, `Vec k` of `SgLinAlg` at `Sg`;
  ⟨η, T⟩ = Σⱼ ηⱼ Tⱼ.  Statistics on a space X are families of signed tests `Fin k → SgT X`, as random vectors in plan 05.
- **Discrete families in multiplicative form.**  The discrete model has no exp or log, so a discrete exponential
  family is p(x | θ) = h(x) · ∏ⱼ θⱼ^{Tⱼ(x)} · c(θ) with T : X → Fin k → ℕ (natural parameter θⱼ = e^{ηⱼ}); this is the
  shape of `likSeq-counts`.  Sums of statistics become sums of exponents.
- **Continuous families.**  Base measure h (s-finite) on X; the unnormalised density is the weight e^{⟨η, T⟩}, built
  from the signed exponent s = s⁺ − s⁻ as e^{s⁺} · e^{−s⁻} (`Exp`, `NegExp`), so no subtraction of weights is needed.
  The partition function is Z(η) = ∫ e^{⟨η, T⟩} dh.  Normalisation uses a normaliser n with Z · n ≈ 1 (no division),
  and the log-partition A(η) = log Z(η) is a signed value, defined when 0 < Z < ∞ (`SignedLog.logS`).
- **KL between members of one family** is the library's `KL` with base P_{η₂} and the density ratio
  dP_{η₁}/dP_{η₂} = e^{⟨η₁ − η₂, T⟩} · Z(η₂)/Z(η₁), itself an exponential weight, so no division of densities is
  needed and Gibbs (`KL-nonneg`) applies directly.
- **Sufficiency is Bayesian.**  A statistic S is sufficient (for a given model and every prior) when datasets with
  equal S have ≈ posteriors.  This is the notion the PAIRS paper's argument needs for exponential families and it is
  statable with what exists; the frequentist notion (the conditional law of the data given S is free of θ) needs
  disintegration (see "Out of reach").
- **Cauchy's equation is algebra first.**  The elimination of h̃, additivity of the centred map, and the extrapolation
  to every N are identities in any commutative ring (constructive, no LEM).  Affinity (additive ⇒ linear) needs a
  regularity hypothesis and the order structure of the reals, and is a separate item.
- Constructive where possible: `Analysis/ExpFamAlg`, `Analysis/CauchyAlg` and the algebraic part of the PAIRS theorem
  use no `lem`/`lem₁`; LEM only in modules that integrate.
- Avoid records inside parameterised modules (check cost); Σ types or top-level records.

## Phase A: exponential families

- 56 `Analysis/ExpFamAlg` (constructive, any commutative ring): sums of statistic vectors over `Fin N`;
  ⟨η, Σᵢ Tᵢ⟩ = Σᵢ ⟨η, Tᵢ⟩; the log-partition of N draws, N · A; the conjugate update (χ, ν) ↦ (χ + Σᵢ Tᵢ, ν + N)
  and its sequential composition (updating on xs then on ys is updating on both).
- 57 `Inference/ExpFamily` (needs 56, `Inference/Bayesian`; discrete): the multiplicative family; product-likelihood
  factorisation through Σ T (generalising `likSeq-counts`); the natural conjugate prior ∝ ∏ⱼ θⱼ^{χⱼ} c(θ)^ν and the
  posterior update χ + Σᵢ T(xᵢ), ν + N (via `sequential`); Bayesian sufficiency of (Σᵢ T(xᵢ), N); Bernoulli as an
  instance, recovering `likSeq-counts`.
- 58 `Continuous/ExpWeight` (enabler; lem₁): the weight e^{s} of a signed value and of a signed test as a morphism
  into WQ; e^{s + t} ≈ e^{s} e^{t}, e^{0} ≈ 1, congruence under ≃ and ≐, positivity and boundedness for bounded s,
  log(e^{s}) ≃ s (`SignedLog.log-exp`).
- 59 `Continuous/ExpFamily` (needs 58, 43, 46): the family on X for a base measure h, statistic T : Fin k → SgT X and
  natural parameter η : Vec k; Z(η), the normalised probability P_η (by a normaliser), A(η); `product-expFam`: the law of
  N iid draws from P_η is the family on Xᴺ with statistic Σᵢ T ∘ projᵢ, base hᴺ and partition Z(η)ᴺ (so log-partition
  N · A) (`∫-rectⁿ`, `IID`); instances Exp(λ) (T = x, h Lebesgue on the half-line) and the Gaussian with known
  variance (T = x, h ∝ e^{−x²/2}), agreeing with `ExpDist` and `GaussReal`.
- 60 `Continuous/ExpFamilyPost` (needs 59, `CondIID`): conjugate updating on a continuous parameter space Θ: for
  η : Θ ⇒ RQᵏ and A : Θ ⇒ RQ as morphisms, the conjugate prior with density ∝ e^{⟨η(θ), χ⟩ − ν A(θ)} against a base on
  Θ, and the posterior after X_N (the Bayesian joint of `CondIID` reweighted by the likelihood, normalised) is the
  conjugate prior at χ + Σᵢ T(xᵢ), ν + N; Bayesian sufficiency of (Σᵢ T(xᵢ), N).

## Phase B: information geometry

- 61 `Continuous/ExpFamilyKL` (needs 59, `KLDiv`): log p_η ≃ ⟨η, T⟩ − A(η) pointwise; `KL-expFam`, the Bregman form
  D(P_{η₁} ‖ P_{η₂}) ≃ A(η₂) − A(η₁) − ⟨η₂ − η₁, E_{η₁}[T]⟩ for T integrable under P_{η₁}; `convex-A`,
  A(η₂) ≥ A(η₁) + ⟨η₂ − η₁, E_{η₁}[T]⟩ (from `KL-nonneg`; convexity, not strict convexity — see "Out of reach").
- 62 `Continuous/ExpFamilyProj` (needs 61): the Pythagorean identity and moment matching without derivatives.  For a
  probability P = f · h with T integrable under P, and P* = P_{η*} in the family with E_{P*}[T] ≃ E_P[T]:
  D(P ‖ P_η) ≃ D(P ‖ P*) + D(P* ‖ P_η) for every η (`pythagorean-expFam`), where D(P ‖ P_η) is E_P[log f − log p_η];
  hence P* minimises D(P ‖ ·) over the family (`moment-matching-opt`, from `KL-nonneg`).  The identity is linear
  algebra once log p_η is affine in T: both sides reduce to A(η) − A(η*) − ⟨η − η*, E_P[T]⟩.

## Phase C: PAIRS and Cauchy's functional equation

- 63 `Analysis/CauchyAlg` (constructive, any commutative ring, on vectors `Vec l → Vec k`): from
  g(y₁) + g(y₂) ≈ h̃(y₁ + y₂) for all y₁, y₂: `cauchy-reduction`, h̃(y) ≈ g(y) + g(0) and the centred
  ḡ(u) = g(u) − g(0) is additive; ḡ(0) ≈ 0, ḡ(−u) ≈ −ḡ(u), ḡ(n u) ≈ n ḡ(u), ḡ(Σᵢ nᵢ eᵢ) ≈ Σᵢ nᵢ ḡ(eᵢ) for integer
  coefficients, and rational homogeneity where 1/n exists (an `inv` parameter, as in `Analysis/Exp`).  The
  extrapolation to every N, which needs no regularity: Σ_{i≤N} g(yᵢ) ≈ ḡ(Σᵢ yᵢ) + N g(0) (`pairs-extrapolate`, by
  induction on N).  Corollary 3's algebra: Σ_{i≤M} g(yᵢ) ≈ h̃_M(Σᵢ yᵢ) for one M ≥ 2 gives the pair equation (fix the
  remaining M − 2 arguments; `cardinality-reduction`).
- 64 `Analysis/CauchyReal` (needs 63; over `Sg`): `cauchy-affine`: an additive ḡ : Sg → Sg that is monotone, or
  bounded above on an interval, is ḡ(u) ≃ c · u with c = ḡ(1) (rationals first by 63, then the Archimedean
  structure and density of rationals in the cuts); per coordinate, an additive ḡ : Vec l → Vec k with these
  hypotheses on each coordinate map is a matrix, so g(y) ≃ A y + b.
- 65 `Inference/PairsTheorem` (needs 57 or 59–60, 63, 64): Theorem 1 with sufficiency in factorised form.  For an
  exponential family with canonical statistic t*, an embedder t_ω with t* ≈ g ∘ t_ω (sufficiency at N = 1) and the
  pair condition t*(x₁) + t*(x₂) ≈ h̃(t_ω(x₁) + t_ω(x₂)) (the form sufficiency at N = 2 takes for the family):
  (a) for every N, Σᵢ t*(xᵢ) ≈ h̃_N(Σᵢ t_ω(xᵢ)), so datasets with equal (Σᵢ t_ω(xᵢ), N), equivalently equal mean pool
  and N, have ≈ posteriors (Bayesian sufficiency at every N, by 57/60); (b) under the regularity of 64,
  t* ≃ A t_ω + b.  `cardinality-invariance` (Corollary 3): the same conclusions from {1, M} for any M ≥ 2.  Part (a)
  needs only 63 and is placed first.

## Phase D: polynomial families and the Barron–Sheu side

- 66 `Continuous/ExpSieve` (needs 59, 62, `PolyTest`): `poly-expFam`, the polynomial exponential family on [0, 1] with
  T_k(x) = (x, x², …, x^k) against the uniform base; `moment-matching-opt` specialised: if some member has the moments
  E[Xʲ] ≃ E_f[Xʲ], j = 1 … k, it minimises D(f ‖ f_k(· ; θ)) over the family (62).  The link to PAIRS (a k-dimensional
  mean-pool embedder tracks empirical moments, and by Barron–Sheu these approximate the true density at rate
  O(k^{−2r})) is recorded as documentation in the module header, not as a theorem (the rate is out of reach).

## Order of agents

| Round | Agent 1 | Agent 2 |
|---|---|---|
| 1 | 56 → 57 | 58 → 59 |
| 2 | 60 | 61 → 62 |
| 3 | 63 → 65a | 64 |
| 4 | 65b | 66 |

65a is part (a) and the cardinality reduction (needs 57 or 60, and 63); 65b is part (b) (needs 64).

## Out of reach (kept, with the reason)

- **Sufficiency in the general sense, and the step "sufficient at N = 2 ⇒ pair equation".**  The paper derives
  g(y₁) + g(y₂) = h̃(y₁ + y₂) from sufficiency of the mean pool at N = 2 and minimality of t*.  The frequentist
  definition (the conditional law of the data given S does not depend on θ) needs conditional distributions given a
  random variable, i.e. disintegration, which the library lacks (plan 05 already puts general conditional
  independence out of scope for the same reason); minimality needs identifiability arguments on the family.  Here the
  pair equation is a hypothesis (item 65) and sufficiency is Bayesian.
- **The Fisher–Neyman factorisation theorem in full.**  Factorisation ⇒ Bayesian sufficiency is in 57/60.  The
  converse (sufficiency ⇒ factorisation of the density) needs Radon–Nikodym derivatives and conditional expectations;
  the library only has densities given explicitly.
- **Corollary 2 (Koopman–Pitman–Darmois).**  Needs smooth densities with support independent of θ, differentiation in
  x, and a functional-equation argument on the log-likelihood over open sets; none of the analysis (partial
  derivatives of densities, open sets of Rᵏ) exists.
- **Strict convexity of A, and E_η[T] = ∇A(η).**  Strictness needs the equality case of Gibbs (KL = 0 ⇒ equal laws:
  equality in x log x ≥ x − 1 almost everywhere, and uniqueness of measures from integrals, which needs π-λ) and a
  minimal statistic.  ∇A = E[T] needs differentiation under the integral sign for parameter integrals in general
  (dominated convergence for difference quotients); `DerivMoment` covers specific cases only.
- **Moment matching as stationarity of the KL** (the derivative form of `moment-matching-opt`).  Needs ∇A as above.
  Replaced by the derivative-free Pythagorean route (62), which gives the stronger conclusion (global minimiser).
- **Existence of the information projection** for a general subfamily or a general f.  Needs existence of a
  minimiser (compactness or lower semicontinuity of KL, convexity of the moment set); 62 proves the characterisation
  (a moment-matching member is the minimiser), not existence.
- **Continuity as the regularity in Cauchy's equation.**  Continuity of Sg-valued maps (pairs of lower cuts) has no
  definition in the library; 64 uses monotonicity or local boundedness, which imply the same conclusion.  Continuous
  versions follow if a notion of continuity on Sg is added.
- **The Barron–Sheu rate D(f ‖ f_k) ≤ O(k^{−2r}).**  Needs Sobolev spaces Hʳ, Jackson-type polynomial/spline
  approximation bounds in sup-norm, the bound relating KL to the sup-norm error of the log-density, and existence of
  the moment-matching solution (strict convexity of A on the family); none of this approximation theory exists.  66
  keeps the family and the minimiser characterisation, which are the parts the rate is built on.

## Guardrails

- Algebraic identities stay over abstract commutative rings (`Analysis/ExpFamAlg`, `Analysis/CauchyAlg`) and are
  connected to the concrete cuts by bridge lemmas: unfolding cut operations in goal types has cost orders of magnitude
  in check time (`docs/Architecture.md`, `docs/History.md`; plan 05's `GaussVector` exhausted 3 GB comparing `covM`
  terms).
- Declarations within `scripts/longdecls.py` defaults: 18 lines, 1000 characters, 130 columns; split long derivations
  (centring, elimination of h̃) into named helpers.
- `--safe --without-K`, no postulates.
- Verification per module: typecheck the touched modules alone from the command line (checking the exit status),
  `python3 scripts/modindex.py`, `make doccheck`, `make longcheck`.  No cold `make check` or `make progress`.
