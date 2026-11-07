# Audit: `continuous-distributions`

Reading audit (no Agda run). Files under `src/QBS/Continuous/`; line numbers are from the current tree.
I read headers and top-level statements of all 41 modules and skimmed the proofs of the moment chain.

## 1. Summary

The domain builds concrete distributions on the continuous model in three layers.
(a) Lebesgue measure on [0,inf) is the s-finite sum of unit intervals `n + U` (`HalfLine.agda`); with
`reweightPre` and `normPre` this gives "density x base measure, normalised" (`DensityDist.agda`,
`ExpDist.agda`, `RealDensity.agda` for symmetric densities on `RQ`).
(b) Integrals are computed by one engine, the tail FTC / integration by parts on the half-line
(`TailFTC*`, `DerivBridge`), fed with exponential or Gaussian algebraic facts: `int x^n e^{-x} = n!`,
`int x^j e^{-x^2/2}` recursions, the Gaussian normaliser `Z` left abstract and shown invertible and finite.
(c) The uniform distribution is the fair coin pushed along the binary expansion, with its CDF, mean, second
and n-th moments, variance, the Beta integral and the sampling/estimation consequences (`UniformSample`,
`UniformInterval`).

The main finding is that the exponential moment theorem is proved **five times** (HalfLineMean,
HalfLineMoment2, HalfLineMomentN/MomentFact, DerivMoment, and ExpRateMoment for rate lambda) and the
uniform moments are proved **four times** (UniformMean, UniformMoment, UniformMomentN, UniformVariance), each time with
its own algebra. Recommendations, in order:

1. Retire `HalfLineMean`, `HalfLineMoment2`, `ExpDistSq` proofs (and `HalfLineUnit`/`HalfLineNorm`/`GeometricNorm`
   self-similarity machinery where it is used only by them) in favour of `HalfLineMomentFact` or, better,
   `DerivMoment`; keep one route and state n=0,1,2 as corollaries (about 1,000 lines).
2. Make `DerivMoment`/`DerivBridge` the single route for every half-line integral (exp, rate-lambda, Gaussian);
   `ExpRateMoment` (258 lines) re-does the 300-line `PolyExpCert` shifting by hand which `DerivMoment`'s own header says the
   calculus replaces.
3. Introduce a generic "density distribution" interface (`DensityDist` already is one) with
   `Moment`-style corollaries and instantiate it for `expDist`, rate-lambda, half-normal, real Gaussian; today
   `ExpDist.agda` re-does `DensityDist` by hand (`massP-expW`, `mass-inv`).
4. State location-scale results once, as a pushforward lemma along an affine `Hom` (`UniformInterval` and
   `HalfLineScale`/`HalfLineRate.scaleH` are two special cases proved separately).
5. Collapse per-module copies of tiny helpers (`negExp-cong`, `bd1`, `hm`, `half<=1`, `fact`, `two`).

## 2. Main results

| Result | Where | Plain statement | Findable? |
|---|---|---|---|
| `lebPre`, `integral-leb` (`∫ᴹ-leb`) | HalfLine.agda (module header l.2-13) | Lebesgue on [0,inf) is `sum_n (n+U)` | Interface/Modules yes; header good |
| `densDist d nrm`, `∫-dens` | DensityDist.agda:~20-63 | normalised density d on [0,inf) is a probability `Pre` with `int f = int d f dlambda` | Modules.md:245; **not in Interface.md** (only appears via ExpMomentN/idD uses) |
| `expDist`, `∫-expDist-one`, `∫-expDist-id` | ExpDist.agda | Exp(1): mass 1, mean 1 | Interface.md:175; good |
| `∫-expDist-sq` | ExpDistSq.agda | E[X^2]=2 | Interface.md:180; fine |
| `∫ᴹ-pw-moment` : `int x^n e^{-x} = n!` | HalfLineMomentFact.agda:96 | all exp moments | Interface.md:206; good, but 4 other proofs |
| `∫ᴹ-leb-negExpR` etc. : `lambda int e^{-lambda x}=1`, `lambda^{n+1} int x^n e^{-lambda x}=n!` | ExpRateInt, ExpRateMoment | rate-lambda exponential | header good; Interface entry should be checked, rate version is the usable one |
| Gaussian `moment-succ`, `even-moment`, `Z`, `Z-inv`, finite `Z <= 4` | GaussMoment:96,122; GaussFinite:80; GaussInverse:124 | half-normal moments without pi; normaliser finite and invertible | Interface.md:208-214 good |
| half-normal mean | GaussMean(Unit) | `int x phi = 1` | Interface.md:246 |
| `symDist` (RealDensity `Sym`) | RealDensity.agda | symmetric density on R | header good, Interface weak |
| `uniform`, mean `1/2`, `E[u^2]=1/3`, `E[u^n]` | Uniform, UniformMean:105, UniformMoment, UniformMomentN | uniform on [0,1] | Interface.md:263-267 |
| CDF `F t = t` | UniformCDF.agda:104-139 | uniform CDF is the identity | check Interface (not seen in grep of "Uniform CDF") |
| `beta-closed`, `beta-conj` | BetaIntegral | `(k+m+1)! B(k,m) = k! m!`; conjugacy | Interface.md:269 |
| tail FTC `glue`, `glue-D`, `ftc-J` | TailFTCLipHalf, DerivBridge, TailFTCLipJ | integration by parts on [0,inf) from a dyadic certificate | Interface.md:195-198, 253; two near-parallel routes |
| `sample-mean-unbiased`, `sample-variance-unbiased` (uniform on [a,b]) | UniformSample, UniformInterval | unbiased estimators for the uniform | Interface.md:151; ok |

## 3. Documentation

- **Names say less than contents.** `Continuous.TailFTC*` (8 modules) live in the "distributions" domain but are
  general calculus; `GaussHalfLine` is "part 1" of the Gaussian moments and not a half-line module.
  `HalfLineMomentFact` is the final exponential-moment theorem, `HalfLineMomentN` its toolbox. `UniformInterval` is
  an estimation module, not a distribution. Proposed headers:
  - `HalfLineMomentN`: "Unit-interval identities for `x^j e^{-x}`; the engine used only by `HalfLineMomentFact`. Reader: go to `HalfLineMomentFact` for the theorem."
  - Each of `HalfLineMean`, `HalfLineMoment2`: add "Superseded by `HalfLineMomentFact.∫-x` / `∫-x²`; kept as an independent check", or delete (recommendation 1).
- **Add to Interface.md** a short "Distribution recipe" entry before the per-distribution lists:
  "Every continuous distribution is `normPre (reweightPre d base) n` for a base `lebPre`/`lebR`/`fairCoin` and a density `d`; its mass
  is `∫ᴹ base d`, its integrals are `∫ᴹ base (d · f)` (`DensityDist.∫-dens`); moments are `∫ᴹ base (d · xⁿ)`, computed by the
  half-line integration by parts `TailFTCLipHalf.glue` / `DerivBridge.glue-D`." Currently the recipe is only visible by
  comparing ExpDist's and DensityDist's headers.
- `DensityDist` header says "(generalising `Continuous/ExpDist`)" but `ExpDist` does not import it; say so or make it do so.
- A table in Guide.md mapping each distribution to (density, base, normaliser, mean, second moment, where) would orient an outsider.
- `Uniform.agda` has no mention of its CDF/moment modules; add a "see also" line.

## 4. Simplification

1. **Exponential moments proved five ways.**
   `HalfLineMean` (242 lines, self-similarity recursion `KK-pt`/`KK-pf`, l.120-137), `HalfLineMoment2` (297 lines,
   `LL-pt-true`, l.133), `HalfLineMomentN` + `HalfLineMomentFact` (196+122), `DerivMoment` (68, whose header calls it "validation" of
   the 150-line shifting it replaces), `ExpRateMoment` (258). All prove `int x^n e^{-x} = n!` (n=1,2 additionally in
   `∫-x`, `∫-x²` of MomentFact:~110, re-deriving MomentFact's own old results).
   Proposal: keep `DerivMoment` as the theorem, derive `∫-x`, `∫-x²`, `ExpDist` mean/second moment from `moment-succ`; delete HalfLineMean,
   HalfLineMoment2, HalfLineUnit (unless used by GeometricNorm/ExpRate*; grep before deleting), HalfLineMomentN.
   Gain: roughly 800-1,100 lines and several compile-heavy modules gone (these are the self-similar modules, the slow ones).
   Cost: Interface.md entries 171, 184-185, 206 rewritten; dependents `ExpDistSq`, `Inference.ExpDist*` need re-pointing.
   Risk: `DerivMoment` is imported by nothing today; check it compiles at the same cost and does not rely on `HalfLineMomentN` facts
   (it does import the exponential facts of `HalfLineMomentN`, which then must move into `TailFTCExp*` or `Analysis/DerivExp`).
2. **Rate-lambda moments via `DerivMoment`.** `ExpRateMoment` repeats the `AtInterval`-style shifting. Port the rate-lambda case to
   `Deriv` certificates (chain rule `Analysis/DerivChain` handles `x -> lambda x`), then `ExpRateInt` becomes the n=0 case. Alternatively
   derive rate lambda from rate 1 by the change of variables `HalfLineScale.dblH`/`HalfLineRate.scaleH` already provide
   (`∫ h(lambda x) = c ∫ h`), which also gives the Gamma family for free. This is the location-scale lemma (item 4).
3. **Generic density-distribution instance.** `ExpDist.agda:55-60` (`massP-expW`, `mass-inv`) is exactly `DensityDist.massP-densW`/`mass-inv`
   (l.43-47) with `d = negExpH`. Define `expDist = densDist negExpH expNrm` (Inference `idD`/`sqD` already do this, Interface.md:184).
   Then `ExpDist`+`ExpDistSq` collapse to instances `E-atᴵ-dens`, removing parallel statements. Also `RealDensity.Sym` and
   the half-normal are `densDist` instances with `n` the inverse of `Z`; one record/module
   `Dist : Set where field d; nrm; ...` (or a parametrised module) would hold the recipe once. Cost: low, interface unchanged
   if `expDist` is kept as an alias.
4. **Location-scale once.** `UniformInterval` (affine map `Y = a + cX`, estimation moments by `Analysis/Estimator` affine part),
   `HalfLineScale` (`dblH`, `half-two` l.83), `HalfLineRate.scaleH` and `RealShift/RealScale` (in `continuous-lebesgue`) are all
   pushforward along `x -> a + c x`. State "law of `a + c X` has moments given by those of `X`" once at the `Pre` level
   (the monad's `map` of an affine `Hom`) and instantiate for uniform [a,b], rate-lambda exponential, N(mu,sigma^2). Gain: removes
   per-distribution scale proofs and gives the missing N(mu,sigma^2) and Exp(lambda) laws as corollaries. Cost: needs a
   `Hom` for affine maps on `WQ`/`RQ` (partly existing in `RealScale`).
5. **Small helpers redefined per module** (each is 2-6 lines, but they obscure that the facts are shared):
   - `negExp-cong`: GaussMean:77, HalfLineUnit:65, HalfLineMomentN:56, TailFTCExp:42, TailFTCExpHalf:39 (also ExpFamily:343, other domain). Export once from `Analysis/NegExp`.
   - `bd1 : x <= 1 -> x <= natE 1`: HalfLineMomentN:59, HalfLineUnit:86, TailFTCExp:45, TailFTCExpHalf:42.
   - `hm : half*x + half*x = x`: UniformMean:40, UniformMomentN:79; `half<=1`: UniformMomentN:76, GaussInverse:78; `two = 1# + 1#`: GaussInverse, TailFTCExpHalf, RealShiftNull:121-122 (use `Analysis/Half`/`Archimedean`).
   - `fact`: BetaIntegral:50 and HalfLineMomentFact:65 are the same definition; BetaIntegral should import it (or both from `Analysis/Series`).
   - the exponential facts `negExp t + t negExp t <= 1 <= negExp t + t`: TailFTCExp:51, TailFTCExpHalf:45, HalfLineMomentN:63, GaussHalfLine `E-b/E-c` (l.76-86), DerivGaussMoment `Eb/Ec` (l.76-79). One lemma in `Analysis/ExpLower`.
6. **Gaussian modules replicate the exponential tower.** `GaussHalfLine`/`GaussMoment`/`GaussMeanUnit`/`GaussMean`/`DerivGaussMoment` follow the same
   shape as `HalfLineUnit`/`MomentN`/`MomentFact`/`Mean`; `DerivGaussMoment` again is the short calculus version. Same advice as item 1:
   keep `DerivGaussMoment` and delete `GaussMeanUnit`'s 192-line pointwise bookkeeping if the calculus covers `x e^{-x^2/2}`
   (header at Interface.md:261 says `∫-xφ` is proved there).
7. **Two tail-FTC routes.** `TailFTCLipHalf.glue` and `DerivBridge.OnHalfLine.glue-D` give the same statement (`DerivBridge` header
   says so); `TailFTCExp`/`TailFTCExpHalf` (87+90 lines) have their own copy of the exponential certificate (`cert-lo`/`cert-hi`)
   as does `Analysis/DerivExp`. Choose `Deriv` as the interface, keep the Lip pack only as its back end.
8. **Uniform moments four ways.** `UniformMean` (`E`, l.101), `UniformMoment` (`e²-true` l.126, `sq-true` l.43), `UniformMomentN` (417 lines, recursion
   `S`, `Z-shift` over generic `nu`), `UniformVariance`. The n-th moment module subsumes the first two (n=1,2); UniformMean/UniformMoment
   should be corollaries, or, via `BetaIntegral`-style recursion `B(k,0)`. Alternatively use the CDF/`F t = t` (`UniformCDF.F-1`, 191 lines)
   and the pushforward law: `E[u^n] = int t^n dF`. Gain: about 300 lines. Risk: UniformMomentN's recursion was probably hand-tuned for compile time; measure.
9. **Hypothesis check.** `ExpRateInt` takes `l` with `l <= natE (suc mu)` and `c <= natE (suc nu)`, extra bounds that follow from boundedness
   (`Bnd`); the `Rat` wrapper re-supplies them. Probably derivable once from `Bnd l`, shrinking every rate signature.

## 5. Categorical language

- `reweightPre`, `normPre`, `sumPre`: the density distribution is Kleisli-like (`d . lambda` is the Kleisli action of the weight monad
  `WQ` on the s-finite monad); `SFiniteReweight` already is this. Do not generalise further: setoid and universe levels
  make a `Monad`-instance restatement of `densDist` costly for no proof gain.
- Location-scale families: a natural transformation / monad `map` (`Continuous/Monad`, `Strong`): law of `f X` = `map f (law X)`. `RealScale`/`RealShift`
  (continuous-lebesgue domain) are the Lebesgue-measure versions; state moments as "`map` of an affine `Hom` preserves `int`", item 4.
- Uniform = `map expansion fairCoin` (`Uniform.agda:43`) is already a pushforward; stating CDF/moments via `∫-map` rather than
  coin integrals with `expansion (consR b r)` cases would shorten UniformMean/Moment.
- `RealDensity` (`RQ = WQ +Q WQ`, density `[d , e]`) uses the coproduct copairing: it is the universal property of the sum,
  correctly used; keep.
- Integration by parts as telescoping `psum a N + g N = g 0 + psum b N` (`TailFTCLipHalf.tele-ibp` l.50, `DerivBridge.sum-ibp0` l.116): same
  statement twice; the second belongs in `Analysis/Series`.
- agda-categories reasoning combinators have no role here (the domain is arithmetic); the `Alg`/algebra modules over abstract
  Archimedean omega-semirings are the right bespoke choice for compile time.

## 6. Open questions

1. Are HalfLineMean/Moment2/MomentN and GaussMeanUnit/GaussMean kept deliberately as independent cross-checks (per `DerivMoment`'s "the old modules stay as checks")? If so, say it in Modules.md and mark them `-- check only`, since outsiders read them as the main proofs.
2. Compile-time of `DerivMoment` versus `HalfLineMomentFact`: is the calculus route faster? If yes, deleting the old tower pays twice.
3. Is `expDist` expected to stay a separate definition (stable API for `Inference.*`), or may it become `densDist negExpH`?
4. Should Exp(lambda) / N(mu,sigma^2) be first-class distributions (with the location-scale lemma), or is the rate-1 / unit scale the intended scope?
5. Where should the Beta/uniform recursion live: with the uniform distribution (`continuous-distributions`) or with the Bayesian examples that use it (Interface.md:142)?
