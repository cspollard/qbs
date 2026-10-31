{-# OPTIONS --safe --without-K #-}

-- Unbounded integration (`Analysis/Unbounded`) for the extended non-negative reals as lower cuts.
module QBS.Analysis.UnboundedLowerReals where

open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.LowerRealsMin using (lowerRealsMin)
open import QBS.Analysis.Unbounded using (module Unbounded)
open import QBS.Classical using (LEM₀)

module LowerRealsUnbounded (lem : LEM₀) where
  open Unbounded (LowerRealsOmega lem) (lowerRealsArch lem) (lowerRealsMin lem) public
