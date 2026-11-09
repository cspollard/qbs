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
--   Concrete models (discrete, continuous, inference, examples, Borel source) are stashed outside the build in
--                    `reference/QBS/…` on this branch; they are not on the Agda include path.
--
-- Start with `IsStatisticalQBSLike` for the abstract statement.
module QBS where

------------------------------------------------------------------------
-- The category of quasi-Borel spaces

-- A random source (the "reals" R, measurable maps R → R, measurable countable partitions), quasi-Borel spaces over it,
-- and their homs.  The source is built from setoid-map helpers, the measurable maps, probes and the source itself.
import QBS.SetoidMaps as SetoidMaps
import QBS.MeasurableMaps as MeasurableMaps
import QBS.Probes as Probes
import QBS.RandomSource as RandomSource
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
import QBS.RandomElements as RandomElements

------------------------------------------------------------------------
-- Probability and soft conditioning, abstractly

-- `ProbabilityInterface`: a commutative strong monad T on a cartesian closed category with a probe object ℛ, whose
-- global elements `measure μ : 1 ⇒ T ℛ` are the probability measures on ℛ, with Fubini over a splitting ℛ ≅ ℛ × ℛ.
import QBS.Probability as Probability

-- `ProbMonad CC` (`CommMonad`): a commutative monad on a cartesian closed category.  `StrongPoint`: its strength at
-- global elements, generic over any such monad.
import QBS.CommMonad as CommMonad
import QBS.StrongPoint as StrongPoint

-- `StatisticalInterface`: weights (`Weights`, a commutative monoid with zero), a measure monad with `score`, countable sums and
-- scaling, and `normalize : M X ⇒ Prob X + 1`.  `StatisticalLemmas` has bind linear in the measure.
import QBS.Statistical as Statistical
import QBS.StatisticalLemmas as StatisticalLemmas

-- `IsQBSLike` and `IsStatisticalQBSLike`: the minimal structure for probability the QBS way, and for soft conditioning;
-- `Instance` gives them for `QBSCat S` from the monads.
import QBS.IsQBSLike as IsQBSLike
import QBS.IsStatisticalQBSLike as IsStatisticalQBSLike
import QBS.Instance as Instance
