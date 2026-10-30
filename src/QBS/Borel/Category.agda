{-# OPTIONS --safe --without-K #-}

-- QBS over Cantor space: the category of quasi-Borel spaces (HKSV, Def. 7), with everything
-- proved for an arbitrary random source specialised to the Borel structure.
module QBS.Borel.Category where

open import Level using (zero; suc)
open import Data.Nat.Base using (ℕ)

open import Categories.Category.Core using (Category)
open import Categories.Category.Complete using (Complete)
open import Categories.Category.Cocomplete using (Cocomplete)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
import Categories.Category.CartesianClosed.Canonical as Canonical

open import QBS.Category using (QBSCat)
import QBS.Limits as L
import QBS.Colimits as C
import QBS.Complete as Cmp
import QBS.Exponential as E
open import QBS.Borel.Source

-- the category of quasi-Borel spaces over the Borel structure of Cantor space
QBS-Cantor : Category (suc (suc zero)) (suc zero) (suc zero)
QBS-Cantor = QBSCat cantorSource

complete : Complete (suc zero) (suc zero) (suc zero) QBS-Cantor
complete = Cmp.complete cantorSource

cocomplete : Cocomplete (suc zero) (suc zero) (suc zero) QBS-Cantor
cocomplete = Cmp.cocomplete cantorSource

cartesianClosed : Canonical.CartesianClosed QBS-Cantor
cartesianClosed = E.cartesianClosed cantorSource
