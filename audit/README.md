# Audit (2026-11-07)

A review of the library for consolidation, simplification, and accessibility to readers from outside the project.
Each domain below has one report, `audit/<domain>.md`, written by one agent from the brief in this file.  The reports
are recommendations: nothing in `src/` or `docs/` is changed by the audit itself.

## Brief (for each domain agent)

Read first: [README.md](../README.md), [docs/Contributing.md](../docs/Contributing.md),
[docs/Architecture.md](../docs/Architecture.md), and the parts of [docs/Interface.md](../docs/Interface.md),
[docs/Guide.md](../docs/Guide.md) and [docs/Modules.md](../docs/Modules.md) that cover your modules.  Then read the
header comment and the top-level statements of every module in your domain (the list is below); read proofs where a
simplification looks likely.

Write `audit/<domain>.md` with these sections:

1. **Summary.**  What the domain is for, in a paragraph an outsider (a mathematician who knows measure theory and some
   category theory, but not this library) can follow, and its three to five most important recommendations.
2. **Main results.**  The high-level theorems and definitions of the domain that a reader would come for (usually
   5–15).  For each: the name and `file:line`, a one-line plain statement, the mathematical statement, and whether it
   is easy to find (in Interface.md, Guide.md, a module header) and crisply documented.  Mark the ones that are not.
3. **Documentation.**  Concrete fixes: proposed replacement text for unclear module headers, missing or misplaced
   entries in Interface.md / Guide.md, modules whose name does not say what they contain, places where the important
   result is buried among helpers.  Give the proposed text, not only "improve this".
4. **Simplification.**  Critical, specific suggestions, each with evidence (`file:line`, current statement, proposed
   statement or merge), the expected gain, and the cost or risk (compile time, interface churn, dependents):
   - lemmas that duplicate the standard library, agda-categories, or another module of this library;
   - near-duplicates across modules that should be one generic lemma (generic-then-instantiate);
   - statements that are more specific than their proofs need (generalise), or hypotheses that are never used;
   - helper-module sprawl (`*Alg`, `*Aux`, `*Ring` splits) that could be merged or shared;
   - long proofs that would be shorter with reasoning syntax, a solver, or a better intermediate lemma.
5. **Categorical language.**  Where established categorical notions would serve better than bespoke formalisations,
   both in how main results are stated and typed, and inside proofs.  Candidates: functors, natural transformations,
   (strong, commutative) monads and their Kleisli categories, monad morphisms, adjunctions, (co)limits, cartesian
   closure, monoidal structure, enriched/concrete categories, and the agda-categories reasoning combinators
   (`HomReasoning`, `Categories.Morphism.Reasoning`).  For each: the current formulation (`file:line`), the categorical
   one, the agda-categories module that provides it if any, and whether it is worth doing (cost, universe levels,
   setoid issues, compile time).  Say plainly when the bespoke version is the better choice and why.
6. **Open questions** for the maintainer.

Be critical and concrete; prefer ten well-evidenced findings to thirty vague ones.  Do not repeat what the docs
already say is out of reach (plans/ and the Out-of-reach sections) unless you have a new route.

Constraints:
- Write only `audit/<domain>.md`.  Do not edit anything in `src/`, `docs/`, `plans/` or elsewhere, and do not commit.
- Do not run `make check`, `make progress` or Agda; this is a reading audit.  Use grep and file reads.
- Search only inside this repository and the libraries it depends on:
  `/Users/cspollard/Programming/agda-stdlib/src` and `/Users/cspollard/Programming/agda-categories/src`.
  Never run `find` or `grep -r` over `/` or your home directory.
- British spelling.  Keep the report under about 400 lines.

## Domains

### `abstract`: Abstract layer (the QBS category, probability and statistical interfaces) (20 modules)

`BoolQ`, `Category`, `Category.Cartesian`, `Category.Concrete`, `Category.Forget`, `Category.Measurable`, `Classical`, `Colimits`, `Complete`, `Core`, `Exponential`, `Instance`, `IntegralMonad`, `IsQBSLike`, `IsStatisticalQBSLike`, `Limits`, `Probability`, `Probes`, `Statistical`, `StatisticalLemmas`

### `discrete`: Discrete model and examples (24 modules)

`Example.Bayes`, `Example.Conditioning`, `Example.HardConditioning`, `Example.Probability`, `Example.Program`, `Example.Recipes`, `Model.AdditiveModel`, `Model.AdditiveSemiring`, `Model.BoolModel`, `Model.BoolSemiring`, `Model.Cantor`, `Model.Discrete`, `Model.DiscreteSource`, `Model.Monad`, `Model.Pairing`, `Model.ProbInstance`, `Model.Semiring`, `Model.StatInstance`, `Model.Strong`, `Model.SubProb`, `Model.Sums`, `Model.ViterbiModel`, `Model.ViterbiSemiring`, `Model.WeightClasses`

### `lower-reals`: Lower reals and number foundations (21 modules)

`Analysis.Archimedean`, `Analysis.Cone`, `Analysis.CutSplit`, `Analysis.CutSum`, `Analysis.ExtNat`, `Analysis.Half`, `Analysis.HalfOrder`, `Analysis.LowerInverse`, `Analysis.LowerReals`, `Analysis.LowerRealsArch`, `Analysis.LowerRealsInf`, `Analysis.LowerRealsMin`, `Analysis.LowerRealsNear`, `Analysis.Min`, `Analysis.Omega`, `Analysis.RationalLemmas`, `Analysis.Series`, `Analysis.SeriesSup`, `Analysis.Threshold`, `Analysis.Unbounded`, `Analysis.UnboundedLowerReals`

### `measure-construction`: Measures, Borel structure on Cantor space, the coin integral and Lebesgue measure (48 modules)

`Analysis.BinaryExpansion`, `Analysis.BorelMeasure`, `Analysis.Clopen`, `Analysis.ClopenMeasure`, `Analysis.CoinCont`, `Analysis.CoinFacts`, `Analysis.CoinGrid`, `Analysis.CoinIntegral`, `Analysis.CoinSets`, `Analysis.CoinSimple`, `Analysis.Density`, `Analysis.DigitAlg`, `Analysis.DyadicAlg`, `Analysis.ExpansionCons`, `Analysis.Fun`, `Analysis.Functional`, `Analysis.Indicators`, `Analysis.Interleave`, `Analysis.JFubini`, `Analysis.JParam`, `Analysis.JSum`, `Analysis.Lebesgue`, `Analysis.LevelSets`, `Analysis.Meas`, `Analysis.MeasFun`, `Analysis.Measure`, `Analysis.Mixture`, `Analysis.MixtureN`, `Analysis.OpenMeasure`, `Analysis.Param`, `Analysis.Pieces`, `Analysis.Regular`, `Analysis.Restrict`, `Analysis.Riesz`, `Analysis.SelfSimilar`, `Analysis.Tensor`, `Analysis.Tonelli`, `Analysis.Uniqueness`, `Analysis.UniquenessWeighted`, `Borel.Category`, `Borel.Cells`, `Borel.Cons`, `Borel.Core`, `Borel.Lead`, `Borel.Measure`, `Borel.Merge`, `Borel.PiLambda`, `Borel.Source`

### `analysis-real`: Real analysis: signed values, exponentials, derivative certificates, tail FTC, Gaussian certificates (32 modules)

`Analysis.AffineAlg`, `Analysis.BoundedCancel`, `Analysis.BoundedRing`, `Analysis.Cauchy`, `Analysis.Deriv`, `Analysis.DerivChain`, `Analysis.DerivExp`, `Analysis.DerivGauss`, `Analysis.DerivProd`, `Analysis.Estimator`, `Analysis.Exp`, `Analysis.ExpFamAlg`, `Analysis.ExpLower`, `Analysis.ExpRate`, `Analysis.ExpRateExt`, `Analysis.ExpRateSigned`, `Analysis.ExpTail`, `Analysis.GaussCert`, `Analysis.GaussCertM1`, `Analysis.GaussExp`, `Analysis.GaussTail`, `Analysis.GeometricMoment2`, `Analysis.GeometricNorm`, `Analysis.NegExp`, `Analysis.PolyExpCert`, `Analysis.SgLinAlg`, `Analysis.Signed`, `Analysis.SignedIntegral`, `Analysis.SignedOmega`, `Analysis.TailFTC`, `Analysis.TailFTCLip`, `Analysis.Variance`

### `continuous-signed-info`: Signed tests and expectations, logarithms, entropy, KL, exponential families, random vectors (45 modules)

`Continuous.Entropy`, `Continuous.ExpFamily`, `Continuous.ExpFamilyAlg`, `Continuous.ExpFamilyAux`, `Continuous.ExpFamilyPost`, `Continuous.ExpFamilyPostAlg`, `Continuous.ExpFamilyPostAux`, `Continuous.ExpWeight`, `Continuous.ExpWeightAlg`, `Continuous.FinTest`, `Continuous.InfoProduct`, `Continuous.InfoProductAux`, `Continuous.KLDiv`, `Continuous.LogCore`, `Continuous.LogNeg`, `Continuous.LogRat`, `Continuous.LogRecip`, `Continuous.RandomVector`, `Continuous.RandomVectorAff`, `Continuous.RandomVectorAlg`, `Continuous.RandomVectorDefs`, `Continuous.RandomVectorLaw`, `Continuous.RandomVectorLawAux`, `Continuous.RandomVectorRing`, `Continuous.RandomVectorSum`, `Continuous.RandomVectorSumRing`, `Continuous.SgMoments`, `Continuous.SgSample`, `Continuous.SgSampleAlg`, `Continuous.SgSampleRing`, `Continuous.SignedExpect`, `Continuous.SignedFubini`, `Continuous.SignedInf`, `Continuous.SignedLimits`, `Continuous.SignedLimitsAlg`, `Continuous.SignedLog`, `Continuous.SignedMul`, `Continuous.SignedSq`, `Continuous.SignedTest`, `Continuous.SignedTests`, `Continuous.SignedTransport`, `Continuous.SignedVar`, `Continuous.SignedVarAlg`, `Continuous.SignedVarRing`, `Continuous.XLog`

### `continuous-distributions`: Continuous distributions: half-line, exponential, Gaussian, uniform, moments (41 modules)

`Continuous.BetaIntegral`, `Continuous.DensityDist`, `Continuous.DerivBridge`, `Continuous.DerivGaussMoment`, `Continuous.DerivMoment`, `Continuous.ExpDist`, `Continuous.ExpDistSq`, `Continuous.ExpRateInt`, `Continuous.ExpRateMoment`, `Continuous.GaussFinite`, `Continuous.GaussHalfLine`, `Continuous.GaussInverse`, `Continuous.GaussMean`, `Continuous.GaussMeanUnit`, `Continuous.GaussMoment`, `Continuous.HalfLine`, `Continuous.HalfLineMean`, `Continuous.HalfLineMoment2`, `Continuous.HalfLineMomentFact`, `Continuous.HalfLineMomentN`, `Continuous.HalfLineNegExp`, `Continuous.HalfLineNorm`, `Continuous.HalfLineRate`, `Continuous.HalfLineScale`, `Continuous.HalfLineUnit`, `Continuous.RealDensity`, `Continuous.TailFTC`, `Continuous.TailFTCExp`, `Continuous.TailFTCExpHalf`, `Continuous.TailFTCHalfLine`, `Continuous.TailFTCLip`, `Continuous.TailFTCLipHalf`, `Continuous.TailFTCLipJ`, `Continuous.Uniform`, `Continuous.UniformCDF`, `Continuous.UniformInterval`, `Continuous.UniformMean`, `Continuous.UniformMoment`, `Continuous.UniformMomentN`, `Continuous.UniformSample`, `Continuous.UniformVariance`

### `continuous-lebesgue`: Lebesgue measure on the real line, change of variables, convergence theorems (44 modules)

`Continuous.ChangeOfVariables`, `Continuous.ChangeOfVariablesAlg`, `Continuous.ChangeOfVariablesFn`, `Continuous.ConvEps`, `Continuous.Dominated`, `Continuous.DominatedSigned`, `Continuous.FTCDyadic`, `Continuous.FTCDyadicPiece`, `Continuous.Fatou`, `Continuous.FatouAux`, `Continuous.InfAlg`, `Continuous.Intervals`, `Continuous.LebPlane`, `Continuous.LebesgueDyadic`, `Continuous.LebesgueDyadicAlg`, `Continuous.LebesgueDyadicNat`, `Continuous.LebesgueInterval`, `Continuous.LebesgueIntervalAlg`, `Continuous.LebesgueScale`, `Continuous.LebesgueScaleAlg`, `Continuous.LebesgueShift`, `Continuous.LebesgueShiftAlg`, `Continuous.LebesgueShiftCut`, `Continuous.LipTest`, `Continuous.LipTestAlg`, `Continuous.MonoTest`, `Continuous.MonoTestAlg`, `Continuous.Monus`, `Continuous.MonusAlg`, `Continuous.NullInf`, `Continuous.RQArith`, `Continuous.RQArithAlg`, `Continuous.RealLine`, `Continuous.RealModel`, `Continuous.RealScale`, `Continuous.RealShift`, `Continuous.RealShiftNull`, `Continuous.RealShiftRefl`, `Continuous.SupTest`, `Continuous.TopMulPos`, `Continuous.UniquenessR`, `Continuous.UniquenessRQ`, `Continuous.UniquenessRQAlg`, `Continuous.UniquenessWQ`

### `continuous-core`: Continuous model core: the monad, s-finite measures, products, independence (43 modules)

`Continuous.CoinCoords`, `Continuous.CoinCoordsJoint`, `Continuous.CoinIndep`, `Continuous.DigitCode`, `Continuous.DigitCut`, `Continuous.DigitDecode`, `Continuous.DigitStream`, `Continuous.Exchangeable`, `Continuous.ExchangeableSwap`, `Continuous.ExtNatModel`, `Continuous.FairCoin`, `Continuous.FinProd`, `Continuous.FinProdPair`, `Continuous.FinProdProb`, `Continuous.FirstBit`, `Continuous.FirstBitInf`, `Continuous.IID`, `Continuous.IndepAlg`, `Continuous.IndepRing`, `Continuous.Independence`, `Continuous.Monad`, `Continuous.NatCancel`, `Continuous.ProbInstance`, `Continuous.ProdBridge`, `Continuous.ProdMap`, `Continuous.ProdReweight`, `Continuous.Product`, `Continuous.SFinite`, `Continuous.SFiniteCommute`, `Continuous.SFiniteDecomp`, `Continuous.SFiniteIncl`, `Continuous.SFiniteMonad`, `Continuous.SFiniteNorm`, `Continuous.SFiniteReweight`, `Continuous.SFiniteStat`, `Continuous.SFiniteStatBridge`, `Continuous.SFiniteStrong`, `Continuous.SFiniteSum`, `Continuous.Sample`, `Continuous.Strong`, `Continuous.SubModel`, `Continuous.SubProb`, `Continuous.Weights`

### `inference`: Inference: expectations, Bayesian examples, samplers, estimators, Gaussian laws (60 modules)

`Inference.Bayesian`, `Inference.BernHalf`, `Inference.BernoulliCompare`, `Inference.BoolDist`, `Inference.CoinBayesRisk`, `Inference.CoinBias`, `Inference.CoinPosterior`, `Inference.CoinUniformPrior`, `Inference.CoinUniformPriorN`, `Inference.CondIID`, `Inference.CondIIDCoin`, `Inference.CondIIDCoinStep`, `Inference.CondIIDConst`, `Inference.DensityExpectation`, `Inference.Domination`, `Inference.ExpDistMean`, `Inference.ExpDistPair`, `Inference.ExpDistVar`, `Inference.ExpFamily`, `Inference.ExpMomentN`, `Inference.ExpPushforward`, `Inference.ExpPushforwardAgree`, `Inference.ExpRateDist`, `Inference.ExpRateOne`, `Inference.Expectation`, `Inference.ExpectationExamples`, `Inference.ExpectationInt`, `Inference.ExpectationIntProduct`, `Inference.ExpectationProduct`, `Inference.ExpectationResp`, `Inference.Frequentist`, `Inference.GaussAffine`, `Inference.GaussReal`, `Inference.GaussRealAbs`, `Inference.GaussScale`, `Inference.GaussShift`, `Inference.GaussVar`, `Inference.GaussVarAux`, `Inference.GaussVarPt`, `Inference.GaussVector`, `Inference.GaussVectorAlg`, `Inference.GaussVectorLaw`, `Inference.HalfNormal`, `Inference.HalfNormalMean`, `Inference.IIDLaw`, `Inference.MultiSample`, `Inference.MultiSampleAlg`, `Inference.MultiSampleRing`, `Inference.PolyDomination`, `Inference.PolyDominationOdd`, `Inference.ProductMarginals`, `Inference.PushforwardExpectation`, `Inference.Sampler`, `Inference.ScaleDensity`, `Inference.SymExpectation`, `Inference.UniformExperiment`, `Inference.UniformSampler`, `Inference.WeakLaw`, `Inference.WeakLawAlg`, `Inference.WeakLawCheb`

