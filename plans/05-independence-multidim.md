# Plan 05: independence, iid families, and multidimensional probability (proposed 2026-11-05; rounds 1–4 done on branch `indep`)

Goal: general definitions of independence, iid and conditionally iid families and exchangeability, with the
theorems that make them usable (factorisation, estimator moments, a weak law of large numbers); then random vectors,
covariance matrices and Gaussian vectors.  Item numbers continue plan 03 (last: 42).  Each phase is skeletoned first
(holes, statements, headers), then filled by agents, two at a time, as in plan 03.

## What exists

- Measures: s-finite `C.Pre (XW X)` with `∫ᴹ` and `_≈ᴹ_` (equal integrals on every test; `Continuous/SFinite`);
  probability `Pre X` of the continuous monad, embedded by `SFiniteIncl.ιPre`; push-forward `∫ᴹ-map`, `mapPre`,
  `joinPre`, `∫ᴹ-join`.
- Products, two factors: `Product.prodPre` (s-finite, Fubini both orders `∫-prod`/`∫-prod′`, `∫-rect`, `marg₁`/`marg₂`,
  `prod-cong`); the probability product `ExpectationProduct._⊗ᵖ_` with `E-at-⊗`, `ExpectationIntProduct` (unbounded),
  `SignedFubini.Ex-⊗`.  No lemma relates `ιPre (p ⊗ᵖ q)` to `prodPre (ιPre p) (ιPre q)`.
- Kock's double strength `ψ : T A × T B ⇒ T (A × B)` in `Probability` (so the product of two kernels is a kernel).
- Independence on the coin: `CoinIndep.fairCoin-indep` (evens/odds), `CoinCoords.coord` with **pairwise** independence
  (`J-indep`, `E-indep`); `Sampler.iidExperiment` and `iid-moments` use only pairwise uncorrelatedness.
- `Analysis/Estimator.Moments` asks only for equal means, equal second moments and pairwise uncorrelatedness.
- Conditionally independent flips built by hand: `CoinUniformPriorN.Kn`, `margN` (Laplace's rule).
- Real line: `RealScale.scaleRH`, `RealShift.shiftRH` (constants only).  No addition `RQ × RQ ⇒ RQ` as a morphism.
- Signed layer: `SgT`, `Int`, `Ex`, `Ex∞`, `Int-dom`, `SignedVar` (variance, centring, shift, scale).
- Nothing indexed by `Fin`/`Vec` yet.

## Decisions (proposed)

- **Setting.** Definitions are for s-finite measures and `∫ᴹ` (the general layer), with probability statements
  through `ιPre`; the probability-monad constructions (coin, samplers, kernels) are bridged once (item 44).
- **Random variables** on a probability space P on Ω are morphisms `Hom S Ω Y`; their **law** is the push-forward
  (`mapPre`).  A family of n random variables is a tuple into a finite product.
- **Finite products.** Heterogeneous, indexed by `Fin n`: `ΠQ n Xs` for `Xs : Fin n → QBS S`, defined by recursion on
  n as nested `_×Q_` ending in `1Q` (the shape of `CoinUniformPriorN.Fl`), with projections `projᵢ` and tupling.  The
  homogeneous Xⁿ is `ΠQ n (const X)`.  Measures `⊗ⁿ` by the same recursion over `prodPre`.  (Alternative: nested pairs
  only, no `Fin`; simpler, but coordinates and permutations become awkward.)
- **Independence** of a family is the strong form: the joint law is `≈ᴹ` the product of the marginal laws.  The
  factorisation of expectations is a theorem.  The converse (factorisation on rectangles ⇒ product law) needs
  uniqueness of measures from rectangles (π-λ), out of scope; constructions produce the strong form directly.
  Pairwise independence is a corollary of mutual independence.
- **IID** with law μ: the joint law is `≈ᴹ μ^{⊗n}`.  An iid sequence: every finite prefix is iid.
- **Conditionally iid given a parameter**: a model `Θ ⇒ T (Xⁿ)` whose law at θ is `(K θ)^{⊗n}` for a kernel
  `K : Θ ⇒ T X`; the kernel power `Kⁿ` is built from `ψ`.  General conditional independence X ⊥ Y | Z (given a
  random variable, not a parameter) needs disintegration and is out of scope.
- **Exchangeability**: invariance of the joint law under adjacent transpositions of coordinates (these generate all
  permutations; the full permutation group is not needed for the theorems here).
- **Vectors and matrices of values** are functions `Fin n → Sg`, `Fin m → Fin n → Sg`, with sums over `Fin` in a
  model-independent algebra module (like `Analysis/Estimator`).
- **Random vectors** are families of signed tests `Fin n → SgT Ω`; affine maps act on tests (`_+T_`, `scaleT`,
  `constT`), so the moment calculus needs no arithmetic on RQ as morphisms.  Laws of AX + b on RQᵐ need addition on
  RQ as a morphism (item 55, optional).
- Avoid records inside parameterised modules (check cost, see `Inference/Sampler` header); Σ types or top level.

## Phase A: independence and iid

- 43 `Continuous/FinProd` [done]: `ΠQ`, `projᵢ`, tupling and its laws; `⊗ⁿ` for s-finite measures; `∫-rectⁿ`
  (∫ ∏ᵢ gᵢ(xᵢ) d⊗ⁿ ≈ ∏ᵢ ∫ gᵢ dμᵢ); marginals of `⊗ⁿ` (coordinate i has law μᵢ, for probability measures);
  `⊗ⁿ-cong`.
- 44 `Continuous/ProdBridge` [done]: `ιPre (p ⊗ᵖ q) ≈ᴹ prodPre (ιPre p) (ιPre q)` and `ιPre (mapPre f p) ≈ᴹ` push-forward,
  so the coin, sampler and kernel constructions feed the s-finite layer.
- 45 `Continuous/Independence` [done] (needs 43): `law`; `Indep₂ X Y`, `Indep n Xs` (mutual); factorisation
  ∫ g(X) h(Y) ≈ ∫ g(X) · ∫ h(Y) and its signed form (`Ex-⊗`); functions of independent variables are independent;
  mutual ⇒ pairwise; invariance under `≈ᴹ`; Var(X + Y) ≃ Var X + Var Y for independent X, Y.
- 46 `Continuous/IID` [done] (needs 45): `IID μ n Xs`; iid ⇒ identically distributed and mutually independent; for a signed
  test f with E f² finite, the observations f ∘ Xᵢ satisfy `Estimator.Moments` (integrability of products by
  2|xy| ≤ x² + y²), so the sample mean and sample variance are unbiased for every iid family, with unbounded tests.
- 46b `Inference/IIDLaw` [done] (needs 46, 46a, 47, 50): the estimator theorems for iid families (unbiased sample mean and
  variance, Var Sₙ ≃ n s, the weak law), and for the draws of a sampler at the coin coordinates.
- 47 `Continuous/CoinCoordsJoint` [done] (needs 43, 44): the first n coin coordinates are jointly independent:
  r ↦ (coord 0 r, …, coord (n−1) r) pushes the fair coin to `fairCoin^{⊗n}`, by induction from `fairCoin-indep`;
  corollary: the draws of `Sampler.iidExperiment` are iid in the sense of 46 (upgrading pairwise to mutual).
- 48 `Inference/CondIID` [done] (needs 46): kernel power `Kⁿ : Θ ⇒ T (Xⁿ)` from `ψ`; `CondIID`; the Bayesian joint
  π ⋉ Kⁿ on Θ × Xⁿ and its marginal; `CoinUniformPriorN.Kn` as an instance (Kn ≈ Bernoulli(θ)^{⊗(n+1)}).
- 48a `Inference/CondIIDCoin` [done] (needs 48, 49): `CoinUniformPriorN.Kn` moved to the s-finite measures and Boolⁿ⁺¹ is
  conditionally iid (Kn ≈ Bernoulli(θ)^{⊗(n+1)}), and `margN` is the data marginal, hence exchangeable.
- 49 `Continuous/Exchangeable` [done] (needs 46, 48): `Exch`; iid ⇒ exchangeable (swap invariance of `prodPre`, from `∫-prod`
  and `∫-prod′`); mixtures of exchangeable laws are exchangeable, so conditionally iid under a prior is exchangeable
  (the easy half of de Finetti); `margN` as an instance.
- 50 `Inference/WeakLaw` [done] (needs 46): Markov's inequality c · P{f ≥ c} ≤ E f (the indicator of [c, ∞] is monotone,
  so `MonoTest.monoH` makes it a test); Chebyshev; the weak law in division-free rate form,
  n ε² · P{|Sₙ − nμ| ≥ nε} ≤ σ² (P ≤ σ²/(nε²)).  It needs only `Estimator.Moments`, so it also applies to the
  existing frequentist layer and samplers.

## Phase B: multidimensional

- 51 `Analysis/SgLinAlg` [done] (independent of phase A): vectors and matrices over a commutative ring (instantiated at `Sg`),
  Σ over `Fin n`, matrix–vector and matrix–matrix products, transpose, quadratic forms; associativity,
  distributivity, (AB)ᵀ = BᵀAᵀ, up to the ring's equality.
- 52 `Continuous/RandomVector` [done] (needs 45, 51): `Fin n → SgT Ω` with `Int₂` per coordinate; mean vector; covariance
  matrix Cov(Xᵢ, Xⱼ) = E XᵢXⱼ − E Xᵢ E Xⱼ (products integrable by 2|xy| ≤ x² + y²); symmetry, Cov(Xᵢ, Xᵢ) = Var Xᵢ;
  Var(Σ Xᵢ) ≃ Σᵢⱼ Cov(Xᵢ, Xⱼ); independent coordinates ⇒ diagonal covariance; the affine rule
  mean(AX + b) ≃ A mean + b and Cov(AX + b) ≃ A Cov(X) Aᵀ.
- 53 `Inference/GaussVector` [done] (needs 43, 52): N(0, Iₙ) as `gaussR^{⊗n}` on RQⁿ with coordinates `idT ∘ projᵢ`; mean 0,
  covariance I, E‖X‖² ≃ n; N(μ, AAᵀ) as the random vector AZ + μ, mean μ and covariance AAᵀ.
- 54 `Inference/MultiSample` [done] (needs 46, 52): iid random vectors; the sample mean vector is unbiased and the sample
  covariance matrix (division-free, as in `Estimator`) is unbiased.
- 55 `Continuous/RQArith` (optional enabler): addition RQ × RQ ⇒ RQ and signed scaling as morphisms (measurability on
  the parts), so AX + b is a map RQⁿ ⇒ RQᵐ and the law of a Gaussian vector is a measure on RQᵐ; the push-forward
  principle connects it with 52–53.

**Skeletons, round 1 (2026-11-05).** 43 `Continuous/FinProd` (definitions `ΠQ`, `projQ`, `tupleQ`, `prodT`, `∏ⁿ`,
`prodⁿ`; holes `proj-tuple`, `∫-rectⁿ`, `margⁿ`, `prodⁿ-cong`), 44 `Continuous/ProdBridge` (`ι-map`, `ι-mass`, `ι-⊗`),
45 `Continuous/Independence` (on a probability `C.Pre Ω` through `ιPre`: `law`, `Indep₂`, `Indep`; holes
`Indep₂-sym`, `Indep₂-map`, `Indep-pair`, `∫-indep`, `Int-indep`, `Ex-indep`, `Int₂-indep`, `Var-indep`),
51 `Analysis/SgLinAlg` (over any `CommutativeRing`: `Vec`, `Mat`, `Σ`, `_·_`, `_*Mv_`, `_*M_`, `_ᵀ`, `idM`, `quad`;
holes for the Σ lemmas and matrix laws).

**Outcome, round 1 (2026-11-05).** All holes filled, no statement changed.  44 `ProdBridge`: `ι-map` is `ι-nat`,
`ι-mass` is `prob-mass`, `ι-⊗` integrates both sides to the same iterated integral (`ι-mult`, `∫ᴹ-join`, `ι-strong`
pointwise, `∫-prod′`).  51 `SgLinAlg`: induction on n with short equational steps (no ring solver); extra `Σ-scaleʳ`.
43 `FinProd` adds `mass-prodⁿ`, `fst-law`, `snd-law`; 45 `Independence` goes through new helpers `ProdMap` (`mapM-comp`,
`_×H_`, `swapM`), `FinProdPair` (`pairⁿ`, the two-coordinate marginal of `prodⁿ`), `IndepRing`, `IndepAlg`
((f+g)² ≐ (f²+fg)+(fg+g²) and the variance identity).  `Independence` does not use `ProdBridge`.  Cold times (each
module alone, dependencies built): ProdBridge 7.4 s / 1.1 GB, SgLinAlg 0.8 s, FinProd 5.3 s, ProdMap 4.8 s,
FinProdPair 5.3 s, IndepRing 2.6 s, IndepAlg 10.1 s / 1.1 GB, Independence 24.9 s / 1.6 GB.

**Skeletons, round 2 (2026-11-05).**  `Estimator.Moments` needs a total ring of random variables, which the unbounded
signed tests are not, so item 46 is split: `Continuous/SgMoments` (definitions only, no holes: `natS`, `sumT`, `sqsT`,
`ssT` over `Fin n`, and the hypotheses `Moments P n F μ σ²` as a Σ type), 46a `Continuous/SgSample` (`Int-sum`,
`Ex-sum`, `Int₂-sum`, `Var-sum` ≃ n σ², `Int-ss`, `Ex-ss` ≃ (n² − n) σ²), 46 `Continuous/IID` (`IID`, `IIDSeq`; holes
`IID-law`, `IID-indep`, `IID-map`, `IID-moments`).  47 `Continuous/CoinCoordsJoint` (`coinPre`, `coin`, `coordH`,
`drawH`; holes `coins-iid`, `coins-iidSeq`, `draws-iid`).  50 `Inference/WeakLaw` (`_≤ᵛ_`, the indicator `geW`/`geH`
of [c, ∞]; holes `≤ᵛ-cong`, `geW` and its laws, `markov`, `markov-ge`, `chebyshev`, `weak-law`, `weak-law-rate`); it
uses only `Moments`, so it covers every iid family through `IID-moments`.  Events are tests χ inside the event
(cross-added pointwise bounds), which avoids absolute values of signed tests.  The iid corollaries (unbiased sample
mean and variance, weak law for an iid family: `IID-moments` composed with `SgSample` and `WeakLaw`) are one-liners
left to round 3, since round 2's two agents cannot import each other's modules while holes remain.

**Outcome, round 2 (2026-11-05).** All holes filled, no statement changed.  46a `SgSample`: induction on n with a
general `Ex-sumG`, `crossS` (E[h Σⱼ Gⱼ] ≃ n m) and `sqCons` ((f + g)² from f², f g, g²); helpers `SgSampleRing`
(signed-ring identities `plus1`, `var-step`, `var-final`) and `SgSampleAlg` (pointwise distribution over `sumT`).
46 `IID`: internal helpers only (`fⁿ`, `tuple-fⁿ`, `mapM-prodⁿ`, `Int-≈`/`Ex-≈`).  47 `CoinCoordsJoint`: splits the
coin into evens and odds (`fairCoin-indep`, `merge-evens`/`odds`) and inducts with `coins-step`.  50 `WeakLaw`:
`geW-0` needs no LEM (LEM only in `markov-ge`); `chebyshev` is `chebyshev-at` at c = E g and `weak-law` instantiates
it at c = nμ; helpers `NatCancel` (cancel n+1 on lower reals, via `ExpLower.qinvC`), `WeakLawAlg` (`rate-alg`),
`WeakLawCheb` (`Ex-dev`, `chebyshev-at`).  Cold times (each module alone, dependencies built): SgSampleRing 2.8 s,
SgSampleAlg 9.1 s / 1.2 GB, NatCancel 5.6 s, SgSample 23.9 s / 1.6 GB, IID 11.4 s / 1.3 GB, CoinCoordsJoint 8.4 s /
1.2 GB, WeakLawAlg 8.7 s, WeakLawCheb 10.0 s, WeakLaw 17.7 s / 1.4 GB.

**Skeletons, round 3 (2026-11-05).**  48 `Inference/CondIID` (definitions `ψH`, the double strength as a morphism
`joinT ∘ T τ ∘ σ`; `kpow`; `CondIID`; `jointM`, `margM`, `inner`; holes `ψ-at`, `kpow-iid`, `CondIID-≈`, `∫-joint`,
`joint-snd`, `joint-fst`, `marg-coord`).  Kernels are s-finite (`SFinite.TQ`); the hand-built coin kernel of the
probability monad is moved there by `SFiniteIncl.ιH` in a separate instance module, 48a `Inference/CondIIDCoin`
(`flat`, `coinK`, `KnS`; holes `Kn-iid`, `margN-marg`, `margN-exch`), placed after 49 since it uses `Exch`.
49 `Continuous/Exchangeable` (`swapQ` for adjacent coordinates, `Exch`, `ExchRV`; holes `Exch-≈`, `Exch-marg`,
`prodⁿ-exch` for any s-finite μ, `Exch-mix`, `condIID-exch`, `IID-exch`).  52 `Continuous/RandomVector` (`RV`,
`meanV`, `covM`, `affT`; holes `Int-mul`, `cov-sym`, `cov-diag`, `Int₂-sumV`, `Var-sumV`, `cov-indep`, `RV-aff`,
`mean-aff`, `cov-aff`).  46b `Inference/IIDLaw` (the round 2 corollaries: `obs`, `devS`, `mom`; holes `iid-mean`,
`iid-var`, `iid-ss`, `iid-weak-law`, `draw-mass`, `draws-mean`, `draws-weak-law`).

**Outcome, round 3 (2026-11-05).** All holes filled, no statement changed.  48 `CondIID`: `ψ-at` is `refl` (`ψH`
unfolds to `prodPre`); `∫-joint` needs only `∫ᴹ-join` and `∫ᴹ-map`; extra `margM-int`, `inner-snd`, `inner-fst`;
helper `CondIIDConst` (∫ c ≈ c · ∫ 1).  49 `Exchangeable`: at k = 0, `ExchangeableSwap.swap3` (s ⊗ (t ⊗ r) pushed
along (x, (y, z)) ↦ (y, (x, z)) is t ⊗ (s ⊗ r), for any s-finite s, t, r, avoiding associativity); `Exch-marg` via
`proj-swap`.  48a `CondIIDCoin`: `Kn-iid` through integrals with helper `CondIIDCoinStep` (`nextK-ι`, one step of
`nextK` under ιPre), not through `ψ-at`.  52 `RandomVector`: `Int-mul` by `Int-dom` with f² + g² (pointwise
a b ≤ a² + b² by `MonusAlg.cut-total`); the sum and affine laws by the double-sum expansion `ExBil` and ring lemmas
instead of induction; helpers `RandomVectorRing`, `RandomVectorAlg`, `RandomVectorSumRing`, `RandomVectorSum`,
`RandomVectorAff` (it first repeated `RV`, `meanV`, `covM`, `affT` under primed names; tidied after the round into a shared
`RandomVectorDefs`, re-exported by `RandomVector`).
`RandomVectorSumRing` failed from the command line after the merge (unannotated binders in `step`/`rhs-eq` left
unsolved metas) and was fixed by annotating their types.  46b `IIDLaw`: as the header route.  Cold times (each module
alone, dependencies built): CondIIDConst 4.5 s, CondIID 5.7 s, ExchangeableSwap 4.9 s, Exchangeable 8.1 s / 1.3 GB,
CondIIDCoinStep 26.7 s / 1.3 GB, CondIIDCoin 9.1 s / 1.4 GB, RandomVectorRing 2.6 s, RandomVectorAlg 11.4 s / 1.3 GB,
RandomVectorSumRing 2.7 s, RandomVectorSum 8.4 s, RandomVectorAff 10.6 s, RandomVector 9.2 s / 1.2 GB, IIDLaw
10.3 s / 1.3 GB.

**Skeletons, round 4 (2026-11-05).**  53a `Continuous/FinProdProb` (enabler: `prodPⁿ`, the n-fold product of
probability measures by `⊗ᵖ`; holes `ι-prodⁿ`, `tuple-proj`, `proj-iid`: the projections of p^{⊗n} are iid with law
p).  53 `Inference/GaussVector`, general first: for iid Zs with law μ and a test f with mean m and variance v, holes
`RV-iid`, `mean-iid` (m, …, m), `cov-iid` (v I), `norm2-iid` (n (v + m²)), `aff-mean`, `aff-cov`; then the standard
normal `γ = gaussμ` at s = 1, μ = 0 (`γ-mass`, `γ-i`, `γ-j` defined; holes `γ-em`, `γ-es`), the Gaussian instances
for any iid N(0, 1) family (`gauss-mean`, `gauss-cov` ≈ I, `gauss-norm2` ≃ n, `gaussV-mean` ≈ b, `gaussV-cov` ≈ A Aᵀ)
and the canonical `Nⁿ n = γ^{⊗n}` on RQⁿ (`std-iid` defined; holes `std-mean`, `std-cov`, `std-norm2`).  54
`Inference/MultiSample` (`obsV`, `sumV`, `crossT`, `ssM`, `cross-diag` by `refl`; holes `RV-obs`, `mean-obs`,
`cov-obs`, `RV-sum`, `mean-sum` (n · mean), `cov-sum` (n · Cov), `Int-ssM`, `ss-unbiased` ((n² − n) Cov)).

**Outcome, round 4 (2026-11-05).** All holes filled, no statement changed.  53a `FinProdProb`: `tuple-proj` from
`tuple-∘` (the tuple of the projections of any g is g; plain induction fails since the tail of `projQ (suc n)` is not
`projQ n` on the tail), extra `tlp`.  53 `GaussVector`: extra `mom`, `var-ent`, `cov-ent`, `γ-var`; `γ-es` through
`γ-var : Var ≃ 1` and `second-moment` (a direct `+S-cong` on `Var-gaussμ` exhausted the 3 GB heap); helper
`GaussVectorAlg` (ring-parametric: entries of `idM`, `*M-idM`, `*Mv-0`, `*Mv-cong`, `*M-cong`, variance ↔ second
moment).  54 `MultiSample`: as the header route; helpers `MultiSampleRing` (ring identities) and `MultiSampleAlg`
(transport along the law of each observation, double-sum and cross-product expectations).  Cold times (each module
alone, dependencies built): FinProdProb 8.4 s / 1.2 GB, GaussVectorAlg 0.7 s, GaussVector 29.4 s / 2.0 GB (the
heaviest module of plan 05), MultiSampleRing 3.0 s, MultiSampleAlg 15.1 s / 1.5 GB, MultiSample 9.8 s / 1.2 GB.

**Skeletons, round 5 (2026-11-05).**  Written by an agent, reviewed and corrected.  55a `Continuous/RQArith` (the real
line's arithmetic as morphisms: `copair×ˡ`/`copair×ʳ`, `addW`, `monusP`, `mixH`, `addRH`, `scaleSRH`, `sumRH`, `linRH`,
`rowRH`, `affRH`; holes `map-random` of `copair×ˡ`, `Meas-monus`, `le₂-borel`, `pick-cong₂`, and the `idT` laws
`idT-add`, `idT-scaleS`, `idT-constRQ`, `idT-sumRH`, `idT-linRH`, `idT-rowRH`, `idT-affRH`; all true at infinite
points, since ≐ is absorbing there, but ≐ is not transitive then, so the laws are pointwise case splits rather than
chains).  55b `Continuous/RandomVectorLaw` (split from 55 so that it can be filled in parallel with 55a; holes
`mul-cong`, `RV-≐`, `mean-≐`, `cov-≐`, `Int-law`, `Ex-law`, `RV-law`, `mean-law`, `cov-law`).  Correction at review:
the agent's `RV-≐ : RV P n X → RV P n Y` from X ≐ Y was false, since ≐ does not transfer integrability ((∞, ∞) ≐
anything); it now needs one part of each Y i zero at each point (pull-backs of `idT`), and `mean-≐`, `cov-≐` take both
witnesses; `mul-cong` (products respect ≐) was added for `cov-≐`, checked by brute force over {0, 1, 2, 3, ∞}.  55
`Inference/GaussVectorLaw` (`coordT`, `affLaw`, `Nᴬ M b`, the law of A Z + b for Z ∼ N(0, Iₙ), `Nᴬ-mass` defined;
holes `affLaw-RV`, `affLaw-mean`, `affLaw-cov`, `Nᴬ-RV`, `Nᴬ-mean` ≈ b, `Nᴬ-cov` ≈ A Aᵀ).

## Order of agents

| Round | Agent 1 | Agent 2 |
|---|---|---|
| 1 | 43 → 45 | 44, then 51 |
| 2 | 46a → 50 | 46 → 47 |
| 3 | 48 → 49 → 48a | 52, then 46b |
| 4 | 53a → 53 | 54 (55 if wanted) |
| 5 | 55a → 55 | 55b |

## Risks

- 43: recursion on `Fin n` through `_×Q_` may make the types of `projᵢ` and `⊗ⁿ` slow to normalise; keep the
  recursion in one place and state the laws once.
- 44: `⊗ᵖ` (strength, probability monad) and `prodPre` (double strength, s-finite) are built differently; the bridge
  goes through the integrals (`E-at-⊗`-style), not the definitions.
- 45: the strong definition is only usable if constructions produce it: 47 (coin) and 48 (kernels) are the tests.
- 47: `fairCoin-indep` is stated for the `I`/`Fun` integral of `Analysis`, so the push-forward statement needs the
  bridge from `Fun` to `Meas` tests used by `CoinCoords`.
- 49: swap invariance of `⊗ⁿ` at an inner position needs `prod-cong` and associativity of `prodPre`, which is not yet
  stated (add to 43 if needed).
- 52: covariance needs integrable signed tests on products; `Int-dom` with 2|xy| ≤ x² + y² avoids Cauchy–Schwarz.

## Out of scope

- Conditional independence given a random variable, conditional expectation, disintegration.
- The strong law of large numbers and the central limit theorem (need almost-sure or weak convergence).
- The hard half of de Finetti; uniqueness of product measures from rectangles (π-λ).

Further directions (consistency and the bias–variance decomposition, higher-order examples and de Finetti, a
computable fragment, correctness of inference algorithms) are collected in `plans/06-future-directions.md`.
- Densities and Jacobians in several dimensions, rotation invariance of N(0, I), the density of N(μ, Σ) (also needs π).
