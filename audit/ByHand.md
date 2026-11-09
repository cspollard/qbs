# By-hand notes

Places where the library does something by hand that may be worth simplifying later.

## `ℕˢ {ℓ}` and `glueₛ` (`QBS.Core`)

`ℕˢ {ℓ} = setoid (Lift ℓ ℕ)` exists only so that the index maps of a partition live at the level `ℓ` of the
random source.  Its cost is spread over the library: `glueₛ`, `⇑ℕ`, `Partitions`, the two sources and the
`Continuous/*` and `Model/*` files use `lift` and `lower` by hand.  The standard library has no `A ↔ Lift ℓ A`
isomorphism or lifted setoid to reuse.

Possible simplification: index by `setoid ℕ` at level 0 (`Func A (setoid ℕ)` between setoids of different
levels is fine), so that `glueₛ` loses its `lower` and `⇑ℕ` disappears.  This needs `Probes` generalised from
`Setoid ℓ ℓ` back to `Setoid c e`, because `Partitions.partitions` would be the probes of a level-0 setoid, and
it undoes the `ℕˢ` lift in the files that currently use `lift` and `lower`.  Count the affected sites before
deciding.

(`glueₛ j α` is not plain composition: it is `uncurry α ∘ₛ ⟨ j , id ⟩`, the pairing of `j` with the identity
followed by evaluation, since `r` is used both to choose the piece and to evaluate it.)
