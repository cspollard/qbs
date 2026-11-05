# TODO: qbs

Open work for the library (see `README.md` for what exists). Library layout: `qbs.agda-lib`, sources in `src/QBS/`, `Makefile`.
Plans and per-module outcomes are in `plans/` (the main one is `plans/03-bayesian-frequentist.md`).

Open items come first, easiest first. Finished items are at the end, one or two lines each, with a pointer to the module or plan for detail. Skeleton modules (with holes) live at their final paths: `make progress` accepts them and `make check` does not.

Build targets in brief: `make check` (strict, every module), `make progress` (skeletons allowed), `make doccheck`, `make longcheck` (long declarations), `make html` (HTML docs, formerly `make htmlbuild`), `make htmlserve`, `make profile-tree` and `make profile-QBS.<Module>` (timing).

## Open

- [~] CI for `qbs`: `make check` typechecks every module (Agda 2.7.0.1, stdlib v2.3, agda-categories c2e7c13e; fails on output, postulates, holes). `.github/workflows/qbs.yml` runs `make doccheck` then `make check` on push, pull_request and manual dispatch. Verify the first run on GitHub.
- [ ] Landing page for the GitHub Pages site.  Today `make html` copies `html/Everything.html` to `index.html`, a bare list of imports.
  - Write a literate `src/QBS/Index.lagda.md`, nicely formatted prose for new users.  It should cover what the library is (quasi-Borel spaces, lower reals, the probability interfaces), how to read it, the headline results with links to their modules, and where to start (`docs/Guide.md`, `docs/Interface.md`).  Its code blocks import the key modules, so the links are checked by Agda.
  - Build it as part of the HTML docs.  Run `agda --html --html-highlight=code` on it, which emits Markdown with highlighted Agda code.  Pass that through `pandoc` (with a small stylesheet, linking to Agda's `Agda.css`) to produce `html/index.html`, in place of the current copy of `Everything.html`.  Keep `Everything.html` linked from the page.
  - Add the step to `make html` and install `pandoc` in `.github/workflows/pages.yml`.  Make sure `make check` and `doccheck` handle `.lagda.md` (the `MODULES` list and `scripts/*.py` glob `*.agda`).
- [ ] Small gaps noted in earlier items: `restrictM` (`Analysis/Restrict`) as a morphism of the continuous monad, like `scoreH`; Riesz for sub-probability measures (needs `μ-⊤ ≤ 1` in `BorelMeasure` and `mass` in place of `μ-⊤ ≈ 1` in `CoinSimple.∫-sconst`, `Ind`, `L-one`); disintegration along a continuous observation.
- [ ] Information quantities, follow-ups (plan 03, "Information quantities", out of scope): `log-mul` without positivity and finiteness hypotheses (the `0 · ∞` cases); KL between Gaussians, `KL(N(μ,1) ‖ N(0,1)) = μ²/2` (needs `exp` of a signed argument, completing the square on `RQ`); Fisher information (needs derivatives beyond the `½ⁿ` difference quotients of `SignedLimits.deriv-Ex`); data-processing inequality and chain rules (need disintegration).
- [ ] Inference beyond the first layer (plan 03, "Staging", steps 5–6): Gaussian estimation theorems and Gaussian–Gaussian conjugacy (the pieces exist: `GaussShift`, `GaussVar`, `SignedVar`; no assembled statement yet); confidence intervals, tests, maximum likelihood, Cramér–Rao.
- [ ] Multidimensional probability (plan 03, "Directions: multidimensional", proposed and not started): finite products `Xⁿ` and n-fold product measures; mean vectors and covariance matrices as signed values with the affine rule; Gaussian vectors `N(0, Iₙ)` and `N(μ, AAᵀ)` by construction. Out of scope there: rotation invariance and the density of `N(μ, Σ)` (need Jacobians), uniqueness of products from rectangles.
- [ ] Compile time (see "Compile time" below): the 2026-10-25 baseline (117 modules, about 17 min) predates the signed layer; a cold `make check` on 2026-11-05 took 29 min (322 modules, 0 failures, 1.9 GB peak), with no per-module times. Re-measure per module with `make profile-tree` and `make profile-QBS.<Module>`; the success criterion is every module under 120 s, no definition above about 10 s. Do not run full cold checks casually.
- [ ] (future) Constructive foundations: `lem` is a module parameter, so no theorem is an axiom, but it is used in the lower reals (`near-sup`: `complement`, `cancel`), the fan theorem (`Clopen.Fan`), Borel-membership case splits, resizing and UIP at `Set₁` (`CutSum`), and the signed layer's finiteness decisions. `docs/Classical.md` lists every use and which are inherent; `docs/ConstructiveLit.md` has the literature and routes (valuations on the Cantor locale first). Removing `lem` needs located reals (Cauchy/Dedekind) and a `Fun` without the `complF` constructor, which touches `Fun-scale`, `Mask` and the Riesz pipeline.
- [ ] (future) Dedekind reals from ℚ (about 1.5–3k lines), if values below zero are needed in measures. Signed values on `[0,∞]` are done (see below); measures keep `[0,∞]` values.

## Finished

Newest first within each group.

### Signed layer, Gaussians and information (plan 03, 2026-11-03 to 2026-11-05)

- [x] Information quantities: DONE 2026-11-05 (`Continuous/{SignedVar, Entropy, KLDiv, InfoProduct}` with helpers `SignedSq`, `SignedVarAlg`, `SignedVarRing`, `XLog`, `InfoProductAux`; `Inference/GaussVar*`). Variance, entropy, KL divergence with Gibbs' inequality (`KL-nonneg`), additivity over products, N(μ, s²) with variance s². `SignedVarAlg` check cost 82 s → 9.6 s by solving ring identities over an abstract semiring (plan 03, "Information quantities"). See `docs/Interface.md`.
- [x] Signed layer: DONE 2026-11-04 (`Continuous/{SignedTest, SignedExpect, SignedInf, SignedTransport, SignedLimits, SignedFubini, SignedLog}` and helpers `InfAlg`, `Log*`). Signed tests `f⁺ − f⁻`, expectations `Ex`, values in `(−∞, ∞]` (`Sg∞`), transport along maps, limits, signed Fubini, logarithm as a signed value. Plan 03, "Signed layer".
- [x] Signed dominated convergence: DONE 2026-11-03 (`Continuous/{ConvEps, NullInf, MonusAlg, DominatedSigned}`). Plan 03, "Signed dominated convergence".
- [x] Dominated convergence and Fatou (both ways, tests on any space): DONE 2026-11-03 (`Analysis/LowerRealsInf`, `Continuous/{SupTest, Fatou, Dominated}`). Plan 03, "Dominated convergence".
- [x] Translation, products and the Gaussian N(μ, s²): DONE 2026-11-03 (`Continuous/{RealShift, Product, LebPlane}`, `Inference/GaussShift`; product measures with Fubini, Lebesgue measure on the plane). Plan 03, "Translation and products".
- [x] Tests from function properties and the real line: DONE 2026-11-03 (`Continuous/{MonoTest, LipTest, RealScale, UniquenessRQ, ChangeOfVariablesFn}`, `Inference/GaussScale`; monotone and Lipschitz functions are tests; N(0, s²)). Plan 03, "Tests from function properties".
- [x] Change of variables: DONE 2026-11-03 (`Continuous/{ChangeOfVariables, FTCDyadic}`, `Inference/ScaleDensity`; monotone change of variables with a derivative certificate, via uniqueness on dyadic intervals). Plan 03, "Change of variables".
- [x] Uniqueness of measures on the half-line: DONE 2026-11-03 (`Continuous/{DigitCode, UniquenessR, UniquenessWQ, LebesgueDyadic, LebesgueInterval, LebesgueScale, LebesgueShift}`, `Borel/Cells`). Route in `docs/UniquenessLit.md`.
- [x] Gaussian without π: DONE (`Analysis/Gauss*`, `Continuous/Gauss*`, `Inference/{HalfNormal, GaussReal, GaussAffine}`): moments through the Lipschitz tail FTC and the certificate calculus (`Analysis/Deriv*`), the standard Gaussian on `RQ = WQ +Q WQ`, mean 0 and variance 1.
- [x] Statistical models and estimators: DONE (`Inference/{Sampler, UniformSampler, Frequentist, UniformExperiment, Bayesian, CoinBias, BernoulliCompare}`, `Analysis/Estimator`): bias, variance, mean squared error, unbiased sample mean and variance, Bayesian updating, Bernoulli models; coin examples with a uniform prior (`Inference/Coin*`). Plan 03.
- [x] Negative reals as a signed layer on `[0,∞]`: DONE (`Analysis/{Signed, SignedOmega, SignedIntegral, Variance, BoundedRing}`, then the unbounded layer above). Dedekind reals are not done (see Open).

### Earlier items

- [x] s-finite measure monad for the continuous model: DONE 2026-10-30 (`Continuous/{SFinite*, SFiniteDecomp, SFiniteNorm, SFiniteStat}`; `continuousStat` fills the whole `StatisticalInterface`). A measure is `[α, m, w]` (probe, probability measure, `Meas` density). Hardest item of the first phase; the work log, hole map and literature notes are in the git history of this file (before 2026-11-05) and in `plans/`.
- [x] Unbounded integration: DONE (`Analysis/{Unbounded, Min, LowerRealsMin, UnboundedLowerReals}`; `FunInf h` says every dyadic truncation is a `Fun`).
- [x] Uniform CDF: DONE (`Continuous/UniformCDF`: `cdf : ∫ uniformSub (cdfTest t) ≈ t`), by first-bit decomposition of the fair coin (`Continuous/FirstBit`) and `Analysis/SelfSimilar`.
- [x] Riesz (probability case): DONE (`Analysis/Riesz`: `setFun`, `functional-setFun`, `setFun-functional`). Sub-probability measures: open, see "Small gaps".
- [x] Bayes' rule, discrete: DONE (`Example/Bayes`: `posterior`, `bayes`, normalised by an inverse of the evidence; generic in a `NormalizableSemiring`).
- [x] `Example/Probability`: DONE (`both-true`, `both-mass`; generic in a complete semiring with `half + half ≈ 1`, instantiated by `Additive lem₁`).
- [x] Hard conditioning: DONE, continuous at measure level (`Analysis/Restrict`: `restrictM`, `restrict-split`) and discrete (`Example/HardConditioning`: `condition`, `condition-split`).
- [x] Sub-probability monad for the continuous model: DONE (`Continuous/SubProb`: `ContinuousSub`, `scoreH`, `failPre`; `Continuous/SubModel`: `softUniform`).
- [x] Fair-coin measure on Cantor space: DONE (`Continuous/FairCoin`; evens/odds independence `Continuous/CoinIndep`; uniform distribution `Continuous/Uniform`, mean ½ in `UniformMean`). Pipeline in the README section "The fair-coin measure".
- [x] Additive real-valued normalisable semiring for the discrete model: DONE (`Analysis/CutSum`, `Model/AdditiveSemiring`, `Model/AdditiveModel`).
- [x] `bind` linear in the kernel argument: DONE (`sumK`, `sumK-point`, `bind-sumK` in `StatisticalInterface`; proved in `Model/StatInstance`).

## Compile time

The pathologies that once made single modules take 10 to 70 minutes are fixed, and the lessons are the durable part of this section. The numbers are from 2026-10-25 to 2026-10-30 (117 modules); the library now has over 300.

**Library-wide flag.** `qbs.agda-lib` has `flags: --lossy-unification` (sound; unification of `f a₁…aₙ =?= f b₁…bₙ` tries the arguments first). It took `SFiniteStrong` from 193 s to 5 s, `JSum` 140 s → 4 s, and made `SFiniteStat` check. One fallout: `SFiniteStrong.strength-assoc` needed an explicit implicit argument.

**Lessons** (each cost minutes to hours once):
- *Mixed spellings of one argument.* Records such as `OmegaSemiring`, `Measure`, `QBS` are huge. Comparing two spellings of one term (`DaniellB.lem lem₁ B` vs `lemOf lem₁`, `QBSCat (discreteSource ℓ)` vs a module alias `S`, `Functor.F₀ TF X` vs `TQ X`) makes Agda unfold both (70 min → 4 s in `Riesz`). Use one canonical name per argument, `INLINE` aliases, and `abstract` for witnesses and expensive definitions (`SFinite.TQ` randomness fields, `J`, `mapM`, `joinPre`).
- *`with` on large goals* (`CoinIntegral` once took over 10 minutes; `LowerInverse` 24 s → 3.5 s). Pass the `Σ` to a helper lemma that pattern-matches, or use `proj₁`/`proj₂`.
- *Implicit arguments left to unification* for rationals and signed values: give them explicitly. Fields written as `lemma _ f` unify metas against the unfolded field type (GBs of memory): write one bridge lemma per field at the unfolded form (`SFiniteStat`: 404 s → 126 s).
- *Local names for large terms* (`wmOf p`, `g (wmOf p)` in `SFinite.∫ᴹ-join`) took over five minutes; give each local a type signature or split into named lemmas. `scripts/longdecls.baseline` is now empty; `make longcheck` guards declaration length.
- *Ring identities over concrete cut semirings* are slow; solve them over an abstract semiring and relate by `refl` lemmas (`SignedVarAlg`: 82 s → 9.6 s).
- Wall time under load misleads: use user time and `+RTS -M3G`. Method for a slow module: truncate the file and time each prefix, replace a body by `?`, then compare the same statement at an opaque object vs the real one.

**Baseline (2026-10-25, cold `_build`, `make profile-tree`).** 117 modules, 998 s summed. The ten slowest were `SFiniteCommute` (never finished, now 16 s), `SFiniteMonad`, `SFiniteStrong`, `JParam`, `JSum`, `Continuous.ProbInstance`, `Model.StatInstance`, `Lebesgue`, `Tonelli`, `Model.ProbInstance`; everything else was under 25 s. Raw output is not committed; `profile/summary.md` has the table.

**Ideas not yet tried**, by expected payoff:
1. `Model.ProbInstance.discreteProb` (~22 s) and `StatInstance.discreteStat` (~30 s): the `commutativeMonad` field conversion. Find which two terms are compared (`-v tc.conv`, or normalise both types and diff), then INLINE the remaining private aliases, make `cartesianClosed S` opaque via `abstract`, or give the interface a `CC`-indexed `braided` argument.
2. `Analysis/Lebesgue` (`J-add` 17.5 s, `J-scale` 11.9 s): likely `Fun`/`FunInf` structure conversions, same cause.
3. The s-finite stack (`JParam`, `JSum`, `Tonelli`, `SFinite*`): one definition per module dominated in every module examined; split into named steps.
4. Tooling: user CPU time and the minimum of two runs in `scripts/profile-tree.py`; an `AGDA_RTS` variable in the `Makefile` for `-A`/`-M`; cache `_build` in CI; a CI step failing when a slow module exceeds a recorded budget.

**Measurement plan.** `make profile-tree` checks every module leaves-first with a 120 s limit (`profile/tree.tsv`, resumable; raise `LIMIT` to see dependents of a slow module). Work lowest-depth slow modules first with `make profile-QBS.<Module>` (one of `modules`, `definitions`, `internal` per run); confirm a cause per definition, apply one change at a time, and keep it only if the module gets 20 % faster and the full build does not regress.

## Literature for the s-finite monad (kept from the 2026-10-29 audit)

Vákár–Ong, *On S-Finite Measures and Kernels* (arXiv 1810.01837); Hirata–Minamide–Sato (ITP 2023) and Affeldt–Cohen–Saito (CPP 2023) are cited by title only and were not checked against our statements; Staton (ESOP 2017) for commutativity.
- Decomposition into scaled probabilities (`SFiniteDecomp.scaledLawsPre`): Vákár–Ong Thms 5(1) and 6(2); ours sums pieces of weight at most `n+1` over the level sets of the weight.
- Randomised representation `[α, m, w]`: Vákár–Ong §10–11; our `≈ᴹ` is the integral-level form of their Thm 20.
- Commutativity and Fubini: Vákár–Ong Thms 1 and 4 cite Staton; `SFiniteCommute` uses Tonelli termwise and `bind-sumK` is the series version.
- Normalisation (`SFiniteNorm`): no source treats it as a theorem; `normProb`, `normZero`, `normScale` follow by classical case analysis (`invDec`).
- Disintegration for quasi-Borel spaces is an open problem in the literature; nothing here needs it.
