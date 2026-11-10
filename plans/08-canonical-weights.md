# Plan 08: weights are the scalars `M ⊤` (proposed 2026-11-10)

Replaces plan 07 (weights as data: `SemiringWeights`, `score` as a field, a free additive monad), which was deleted.

## Idea

Fix a commutative additive monad `M` and let `S = M ⊤`.  `S` is an internal semiring: `⊕` from `IsAlgebraic CommMonoid` (in every
context, so internal by Yoneda), `⋆` from the strength, `0 = 𝟘`, `1 = η ⊤ ∘ !`.  Pairs `(W, score : W → S)` of an internal
semiring and a semiring homomorphism form the slice `CSemiring(C) / S`; `(S, id)` is terminal, `(ℕ, unit)` initial.  So
the weights need not be chosen: take `W := S`, and `score` is the identity.

In the code, `scalarCommSemiring` (`Monad.Algebraic.Scalars`) says that `M ⊤` is an internal semiring: a model of the theory
`CommSemiring` (`Theory.Equational.Model`, an object whose hom-sets `Z ⇒ X` carry the operations of the theory naturally in
`Z`).  It is assembled by `fromMonoids` from the additive model (`M-model`, from `IsAlgebraic`), the multiplicative model
`(⋆, 𝟙)` (strength and commutativity), and two interaction laws (distributivity from `⋆-op`, annihilation from `⋆-comm`).
`M` is not `IsAlgebraic CommSemiring`: `⋆` is natural in the context but not linear in the continuation.  Terminality of
`(S, id)` is slice-category general nonsense and is not formalized.

The semiring structure is what makes `M ⊤` a weights candidate, so the multiplicative laws are on the critical path.

## Categories

- `AMnd(C)` (additive monads, morphisms preserve `⊕`, `𝟘`): terminal is `M X = ⊤` (scalars `0`); initial is the free
  commutative-monoid monad `ℕ[X]` (scalars `ℕ`), if `C` has it.  The measure monad is neither; `Prob` is not in it.
- `M ↦ M ⊤` sends `AMnd(C)` to semirings.  For s-finite measures on QBS, `M ⊤ ≅ [0,∞]`.
- Conventional weights `[0,∞]` are terminal only in the slice over `M ⊤` for that `M`.  The modelling choice is the monad
  (s-finite: `[0,∞]`; finite: `[0,∞)`).  No intrinsic universal property of `[0,∞]` is claimed.
- Sub-semirings of `S` (score mono) form a poset inside the slice: the optional way to let a model choose smaller weights.

## Design consequences

- Dropped: `Weights`, `SemiringWeights`, `Global`, `score`, `SoftConditioning`, `Statistical`, the free additive monad,
  `Monad.Additive` (replaced by `Monad.Algebraic` for `CommMonoid`) and the scalars functor into `Semirings`.
- The weights are the scalars `M ⊤`.  The contextual product `⋆` and `scalarCommSemiring` (`IsModel CommSemiring (M ⊤)`) are in
  `Categories.Monad.Algebraic.Scalars`, with no holes.
- Normalization is the predicate "mass is `𝟙`" (`QBS.Monad.Normalized`: `Prob X ↪ M X` is the equalizer of mass and `𝟙`).
  Dividing by mass is not part of the interface.
- `IsQBSLike` and `Instance` carry `additive : IsAlgebraic CommMonoid M` and load.

## Limits

- Countable additivity (monotone convergence, s-finite measures as countable sums) is not captured by the algebraic
  interface; it stays in the concrete layer.
- No free construction in the abstract layer, no Lawvere theory `Mat(W)`, no single Eilenberg–Moore module: `bind-+`
  (additivity in the continuation) says `+_Y` is a morphism of `M`-algebras, which module data over a sum monad does not
  give.  `Monad.Algebraic` states it as naturality of the operations for bind (`op-resp-∘`).

## Literature (in `lit/`)

Coumans–Jacobs, *Scalars, Monads, and Categories* (arXiv 1003.0585): writer = free monad on a monoid (Lemmas 4–6),
additive monads as a property (Def. 16, Lemma 17), `M_S ⊣ E` (Lemmas 23–27).  Hyland–Plotkin–Power, *Combining effects:
sum and tensor*: monads ≃ Lawvere theories.  Plotkin–Power, algebraic operations and generic effects: the framing of
`Monad.Algebraic`.

## Models

`Theory.Equational.Model` defines `IsModel T X` in a category `C`: operations on every hom-set `Z ⇒ X`, natural in `Z` under
precomposition, satisfying the equations (by Yoneda, a Lawvere model `Xⁿ → X` without needing the powers).  Consequences:

- `Monad.Algebraic.Properties.M-model`: for `IsAlgebraic T M`, `IsModel T (M X)` for every `X` (`op-resp-∘` at `k = id`).
  The converse fails: `IsAlgebraic` also makes bind linear in the continuation.
- `Model.Adjoint.transfer`: for `L ⊣ R`, `IsModel T X` gives `IsModel T (R X)`.
- `Model.Exponential.exponential`: `IsModel T X` gives `IsModel T [ A , X ]₀`, so `A → M ⊤` is a semiring (context-dependent
  weights).  Uses the non-canonical `CartesianClosed`; `Canonical.Equivalence.fromCanonical` converts.

`IsModel T (M ⊤)` for the monad's own `T` (commutative monoids) is only the additive structure; the semiring needs the
theory `CommSemiring`, whose multiplication `⋆` is natural in the context but not an algebraic operation of `M`.

## Other algebraic structures

Nothing above uses commutative monoids specifically, only that the Kleisli homs in each context carry a structure and that
`M ⊤` is closed under the product from the strength.  Replace `IsAdditive` (Kleisli enriched over commutative monoids)
by another theory `T` and the scalars `M ⊤` become the corresponding ring-like object, again terminal in its slice, so
the weights again come for free.  Expected new weights: enrichment over abelian groups gives rings, hence signed
measures with weights in `ℝ` (or `ℂ` amplitudes); idempotent monoids (`⊕ = max`) give tropical or Viterbi weights;
dropping `𝟘` and keeping only convex combinations gives `Prob`, whose scalars collapse to `1` (affine), which is why
conditioning needs the additive extension.  What does not carry over verbatim is `Normalization`: invertibility and
"fails on zero" need a notion of mass (division in a field, or a positivity cone for signed measures).  The analogue of `scalarModel` for another `T` needs its own theory of the corresponding ring-like structure
(`CommSemiring` for commutative monoids, a `Ring` theory for abelian groups); there is no construction yet that adds a
multiplication to an arbitrary `T`.

## Open

- Done in `Monad.Algebraic.Scalars` (no holes): `⋆-cong`, `⋆-∘` (change of context), `⋆-identityˡ`, `⋆-op` (linearity in the
  continuation), `⋆-assoc` (only the strong-monad axioms: `σ-bind`, `σ-diag` from `strength-assoc`), `⋆-comm` (Kock's `ψ`
  and `commutes`: `⋆-ψ`, `⋆-ψ′`), and `scalarCommSemiring`.  The strength lemmas are in `Categories.Monad.Commutative.DoubleStrength` (with `ψ`, formerly `QBS.Monad.StrongPoint`).  The full lax monoidal structure of `(M, ψ)` was not needed.
- Check against the model (`reference/QBS/Continuous/SFinite*`): inhabit `IsAlgebraic CommMonoid` and show `M ⊤` is
  `[0,∞]` with the usual sum and product (`0·∞ = 0`).  Not verified.
- Additivity as a property (Coumans–Jacobs Def. 16, `Object.Biproduct` in `Kleisli M`) giving the algebraic structure, so
  instances need not supply `⊕` and bilinearity separately.  Research, optional.
- Update `docs/` for the removed modules.
