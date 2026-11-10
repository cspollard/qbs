# Plan 08: weights are the scalars `M ⊤` (proposed 2026-11-10)

Supersedes the "weights as data" part of plan 07 (`SemiringWeights`, `score` as a field).

## Idea

Fix a commutative additive monad `M` and let `S = M ⊤`.  `S` is an internal semiring: `⊕` from `IsAdditive` (in every
context, so internal by Yoneda), `⋆` from the strength, `0 = 𝟘`, `1 = η ⊤ ∘ !`.  Pairs `(W, score : W → S)` of an internal
semiring and a semiring homomorphism form the slice `CSemiring(C) / S`; `(S, id)` is terminal, `(ℕ, unit)` initial.  So
the weights need not be chosen: take `W := S`, and `score` is the identity.

## Categories

- `AMnd(C)` (additive monads, morphisms preserve `⊕`, `𝟘`): terminal is `M X = ⊤` (scalars `0`); initial is the free
  commutative-monoid monad `ℕ[X]` (scalars `ℕ`), if `C` has it.  The measure monad is neither; `Prob` is not in it.
- `M ↦ M ⊤` sends `AMnd(C)` to semirings.  For s-finite measures on QBS, `M ⊤ ≅ [0,∞]`.
- Conventional weights `[0,∞]` are terminal only in the slice over `M ⊤` for that `M`.  The modelling choice is the monad
  (s-finite: `[0,∞]`; finite: `[0,∞)`).  No intrinsic universal property of `[0,∞]` is claimed.
- Sub-semirings of `S` (score mono) form a poset inside the slice: the optional way to let a model choose smaller weights.

## Design consequences

- Drop `Weights`, `SemiringWeights`, `Global`, `WeightsAt`, `score`, `score-hom`, `SoftConditioning`.  The weights are
  `kleisli-semiring ⊤` (product: Kleisli composition); `Statistical` keeps only `Normalization`, with `scale w m = m ∘ w`.
  The contextual product `⋆` and its laws (`ScalarAlgebra`, one hole) live in `Categories.Monad.Algebraic.Scalars`.
- `src/QBS/Statistical.agda` is hole-free.  `IsStatisticalQBSLike`, `Instance`, `QBS` still use the old
  interface and do not load.

## Other algebraic structures

Nothing above uses commutative monoids specifically, only that the Kleisli homs in each context carry a structure and that
`M ⊤` is closed under the product from the strength.  Replace `IsAdditive` (Kleisli enriched over commutative monoids)
by another theory `T` and the scalars `M ⊤` become the corresponding ring-like object, again terminal in its slice, so
the weights again come for free.  Expected new weights: enrichment over abelian groups gives rings, hence signed
measures with weights in `ℝ` (or `ℂ` amplitudes); idempotent monoids (`⊕ = max`) give tropical or Viterbi weights;
dropping `𝟘` and keeping only convex combinations gives `Prob`, whose scalars collapse to `1` (affine), which is why
conditioning needs the additive extension.  What does not carry over verbatim is `Normalization`: invertibility and
"fails on zero" need a notion of mass (division in a field, or a positivity cone for signed measures).  `ScalarAlgebra T` is already parametrised over `T`.

## Open

- Hole: `scalar-algebra` (strength laws, `op-resp-∘`).  Lemma wanted: `f ⋆ g ≈ g K.∘ f` at `⊤`.
- Check against the model (`reference/QBS/Continuous/SFinite*`): `M ⊤` is `[0,∞]` with `⊕`, `⋆` the usual sum and product
  (`0·∞ = 0`); `scoreH`/`∫ᴹ-score` in `SFiniteIncl` should show `score = id`.  Not verified.
- Update the stale header and item A of plan 07, and `docs/`.
