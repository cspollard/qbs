# Plan 07: additive monads, weights and soft conditioning (proposed 2026-11-10)

Goal: say what soft conditioning is in standard categorical terms, so that proofs reuse known structure.  The target
statement: **soft conditioning on a strong monad `M` is an object of the comma category `const! (Global SW) ↓ Scalars ⊤`,
i.e. a semiring homomorphism `Global SW → End_M ⊤`** (this is `score` and its laws).  When a free additive monad `T_W`
exists, the unique additive monad morphism `T_W ⇒ M` is a consequence, not extra data.  Item numbers continue plan 05/06
(last seen: 55); the labels below are local.

## Picture

- Additive monads form a category `AMnd(C)`: monads whose Kleisli category has `⊕` and `𝟘` with bilinear composition
  (`IsAdditive`), and monad morphisms preserving them.  This is a category of monads, not of algebras.
- Each additive monad has scalars `kleisli-semiring ⊤` (a semiring), functorially: `Scalars ⊤ : AMnd(C) → Semirings`.
- The free additive monad on a semiring `W` is a universal arrow for `Scalars ⊤` (initial in `W ↓ Scalars ⊤`).  For the
  finite-support monad `M_W` this is Coumans–Jacobs, Lemma 27.  The writer monad `W × –` is only the multiplicative half.
- The free monad is not a measure monad (finite support), so it maps into the measure monads without being one.
- Not captured: countable additivity (monotone convergence, s-finite measures as countable sums).  It stays in the
  concrete layer (`Analysis/Lebesgue`).  The interface needs a strength (for `score-mul`), not commutativity.

Literature (in `lit/`): Coumans–Jacobs, *Scalars, Monads, and Categories* (arXiv 1003.0585): writer = free monad on a
monoid (Lemmas 4–6), additive monads as a property (Def. 16, Lemma 17), `M_S ⊣ E` (Lemmas 23–27).  Hyland–Plotkin–Power,
*Combining effects: sum and tensor*: monads ≃ Lawvere theories, `T_L(W × –)` as a tensor of theories (Theorem 12).

## Done

- [x] `Categories.Monad.Additive`: `IsAdditive M` (with derived `⊕-cong`, `⊕-distribˡ/ʳ` and the semiring `kleisli-semiring X`),
  `AdditiveMonad`, `KleisliCM` (the `CM-Category` of agda-categories).  Moved out of `Statistical`.
- [x] `Categories.Category.Instance.Monads` (monads and `Monad⇒-id`), `Categories.Monad.Additive.Morphism`
  (`IsAdditive⇒`, `AdditiveMonad⇒`), `Categories.Category.Instance.Monads.Additive` (`AdditiveMonads`, `Forget`).
- [x] `Categories.Category.Instance.Semirings` (agda-categories has none), `Categories.Functor.Instance.Scalars`
  (`Scalars X`), `Categories.Monad.Additive.Free` (`FreeAdditiveMonad W = Initial (const! W ↓ Scalars)`, a hypothesis type).
- [x] `Categories.Category.Monoidal.Opposite` (supports the comonoids of `Symmetric.Algebra`).
- [x] `QBS.Statistical`: `SoftConditioning` with `score`, universal `score-add` (an equation in `K [ W × W , ⊤ ]`),
  universal `score-mul` (needs `CartStrength`), `score-one`, `score-zero`; derived `scale`, `zero-bind`, `score-add-global`.

Settled, not to be revisited without a reason: no free construction in the abstract layer (`Bag` is hard; agda-categories
is axiomatic too); no Lawvere theory `Mat(W)` (gives semimodule objects but no monad); no single Eilenberg–Moore module
(`bind-+`, additivity in the continuation, says `+_Y` is a morphism of `M`-algebras, which module data over a sum monad
does not give).  An experiment showed `IsAdditive` equivalent to commutative-monoid structure on each `M X`, with
`bind-+` as a hypothesis; it was removed.

## To do

- [ ] A. **Bridge to `Scalars`** (needs the done layer; the key missing link).  `Global SW`: the semiring of global
  elements `⊤ ⇒ W` (pointwise distributivity from the diagonal-relative one); `w ↦ score ∘ w` as a homomorphism
  `Global SW → kleisli-semiring ⊤`; state `SoftConditioning` as the comma object plus a strength, and prove the universal laws
  follow.  Provides: the categorical meaning of `SoftConditioning`, and the connection to `FreeAdditiveMonad`.
- [ ] B. **Docs** (after A).  Header of `Statistical` (still says "stated at global elements"), Guide §4–5,
  `Interface.md`, `Modules.md` (when the full tree is back).  Optional sanity lemma: `score-mul-global`.
- [ ] C. **Instances** (independent; blocked, the working tree has 32 modules).  `IsAdditive` as sums of measures, the
  strength, and the universal `score-add`/`score-mul` for `continuousStat` and the discrete model; check `Instance` and
  `IsStatisticalQBSLike`.  Provides: validation on real models.
- [ ] D. **Inhabit `FreeAdditiveMonad`** for a concrete model (the discrete finite-support monad), to show the
  universal property is satisfiable.  Research, optional.
- [ ] E. **Additivity as a property** (Def. 16, `Object.Biproduct` in `Kleisli M`) ⇒ `IsAdditive`: instances would not
  supply `⊕` and bilinearity separately.  Research, optional.
- [ ] F. **`ScoreIso`**: `score : W ≅ M 1` (the counit of Lemma 27), giving the injectivity `Normalization` needs.  Optional.

Order: A, then B; C in parallel; D, E, F independent.

## Open questions

- Does Lemma 27 hold without commutativity (`kleisli-semiring ⊤` possibly non-commutative)?
- Is `QBSCat` locally countably presentable (HPP's Lawvere-theory constructions)?  Only relevant for D.
- Is `Object.Biproduct` (Karvonen) enough for E without a `CM-Category`?
