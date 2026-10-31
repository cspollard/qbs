{-# OPTIONS --safe --without-K #-}

-- Quasi-Borel spaces in Agda: an overview of the library, one section per area.  The imports below are qualified
-- (`import M as N`), so this module exports nothing; it is the reading order, and checking it checks the main entry
-- points.  One line per module: `docs/Modules.md`; the public names: `docs/Interface.md`; how the layers fit
-- together: `docs/Architecture.md`; a task-oriented tour: `docs/Guide.md`.
--
-- The library follows Heunen, Kammar, Staton and Yang, *A Convenient Category for Higher-Order Probability Theory*
-- (arXiv:1701.02547).  A quasi-Borel space is a set X with a class of "random elements" R → X, for a type R of random
-- sources.  The quasi-Borel spaces over a fixed `RandomSource S` form a category `QBSCat S`.  Probability lives in a
-- monad on that category.  The library states what a probability monad is once, abstractly, and builds two models.
--
--   Abstract layer   `QBSCat S` is complete, cocomplete and cartesian closed, for every random source S, with no
--                    hypotheses.  `ProbabilityInterface` and `StatisticalInterface` describe the measure monads;
--                    `IsQBSLike` and `IsStatisticalQBSLike` bundle them with the category.
--   Discrete model   R = ℕ; measures are weighted countable families over a complete semiring (Boolean, Viterbi,
--                    ℕ∞, additive [0,∞]); the instance is generic in the semiring and has no hypotheses on the monads.
--   Continuous model R = Cantor space 2^ℕ; measures are Daniell functionals on the measurable functions, built up
--                    from the Borel σ-algebra; it has the fair coin, the uniform distribution and the s-finite monad.
--                    It assumes excluded middle and function extensionality as module parameters (`docs/Classical.md`).
--   Inference        Bayesian and frequentist statistics, stated over the abstract interface or the discrete model.
--   Examples         programs in `do`-notation, Bayes' rule, conditioning.
--
-- Start with `Example.Program` for a program that runs, or with `IsStatisticalQBSLike` for the abstract statement.
module QBS where

------------------------------------------------------------------------
-- The category of quasi-Borel spaces

-- A random source (the "reals" R, measurable maps R → R, measurable countable partitions), quasi-Borel spaces over it,
-- and their homs.
import QBS.Core as Core

-- `QBSCat S` as an agda-categories `Category`.
import QBS.Category as Category

-- Finite and then all small limits, finite and then all small colimits.
import QBS.Limits as Limits
import QBS.Colimits as Colimits
import QBS.Complete as Complete

-- Function spaces, and the canonical `CartesianClosed (QBSCat S)`.
import QBS.Exponential as Exponential

-- The space ℛQ of random sources: random elements of X are exactly the maps ℛQ ⇒ X.
import QBS.Probes as Probes

------------------------------------------------------------------------
-- Probability and soft conditioning, abstractly

-- `ProbabilityInterface`: a commutative strong monad T on a cartesian closed category with a probe object ℛ, whose
-- global elements `measure μ : 1 ⇒ T ℛ` are the probability measures on ℛ, with Fubini over a splitting ℛ ≅ ℛ × ℛ.
import QBS.Probability as Probability

-- `StatisticalInterface`: weights (`CommutativeMonoidWithZero`), a measure monad with `score`, countable sums and
-- scaling, and `normalize : M X ⇒ Prob X + 1`.  `StatisticalLemmas` has bind linear in the measure.
import QBS.Statistical as Statistical
import QBS.StatisticalLemmas as StatisticalLemmas

-- `IsQBSLike` and `IsStatisticalQBSLike`: the minimal structure for probability the QBS way, and for soft conditioning;
-- `Instance` gives them for `QBSCat S` from the monads.
import QBS.IsQBSLike as IsQBSLike
import QBS.IsStatisticalQBSLike as IsStatisticalQBSLike
import QBS.Instance as Instance

------------------------------------------------------------------------
-- The discrete model (R = ℕ)

-- Complete semirings, the weight classes (probability, sub-probability, all measures), and the measure monad over them.
import QBS.Model.Semiring as Semiring
import QBS.Model.WeightClasses as WeightClasses
import QBS.Model.Monad as Monad

-- The model of `ProbabilityInterface` and `StatisticalInterface`, and the packaged `IsStatisticalQBSLike`.
import QBS.Model.ProbInstance as ProbInstance
import QBS.Model.StatInstance as StatInstance
import QBS.Model.Discrete as Discrete

-- Concrete weights: Boolean (possibility), Viterbi (max, ×), and the additive extended non-negative reals.
import QBS.Model.BoolModel as BoolModel
import QBS.Model.ViterbiModel as ViterbiModel
import QBS.Model.AdditiveModel as AdditiveModel

-- Sub-probability measures: soft conditioning that discards runs.
import QBS.Model.SubProb as SubProb

------------------------------------------------------------------------
-- The continuous model (R = Cantor space)

-- Cantor space with its Borel σ-algebra is a random source; quasi-Borel spaces over it are those of HKSV.
import QBS.Borel.Source as BorelSource
import QBS.Borel.Category as BorelCategory

-- The extended non-negative reals as lower cuts of ℚ; Daniell functionals; the Riesz–Daniell correspondence between
-- them and σ-additive Borel measures.
import QBS.Analysis.LowerReals as LowerReals
import QBS.Analysis.Measure as Measure
import QBS.Analysis.Riesz as Riesz

-- Integrals of unbounded functions, with Tonelli and Fubini.
import QBS.Analysis.Lebesgue as Lebesgue
import QBS.Analysis.Tonelli as Tonelli
import QBS.Analysis.Tensor as Tensor

-- The probability monad over Cantor space, packaged as an `IsQBSLike`.
import QBS.Continuous.Monad as ContinuousMonad
import QBS.Continuous.ProbInstance as ContinuousProbInstance
import QBS.Continuous.RealModel as RealModel

-- The s-finite measure monad and its `StatisticalInterface`.
import QBS.Continuous.SFinite as SFinite
import QBS.Continuous.SFiniteStat as SFiniteStat

-- The fair coin, and the uniform distribution on [0,1] with its mean, second moment, variance and CDF.
import QBS.Continuous.FairCoin as FairCoin
import QBS.Continuous.Uniform as Uniform
import QBS.Continuous.UniformMean as UniformMean
import QBS.Continuous.UniformCDF as UniformCDF
import QBS.Continuous.UniformVariance as UniformVariance

------------------------------------------------------------------------
-- Inference

-- Bayesian inference: posterior, sequential updating, evidence, the Bernoulli model.
import QBS.Inference.Bayesian as Bayesian
import QBS.Inference.CoinBias as CoinBias

-- Frequentist inference: experiments, statistics, bias, variance, mean squared error; estimation from uniform draws.
import QBS.Inference.Frequentist as Frequentist
import QBS.Inference.UniformExperiment as UniformExperiment

------------------------------------------------------------------------
-- Examples

-- Probabilistic programs in `do`-notation, Bayes' rule, and conditioning.
import QBS.Example.Program as Program
import QBS.Example.Bayes as Bayes
import QBS.Example.Conditioning as Conditioning
import QBS.Example.HardConditioning as HardConditioning

-- Copy-and-paste set-ups for the imports each kind of result needs.
import QBS.Example.Recipes as Recipes
