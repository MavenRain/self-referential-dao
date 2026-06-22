# self-referential-dao

A denotational design (in the sense of Conal Elliott, using Lean 4 in
place of Haskell) of a **UAT-respecting self-referential DAO**.

The design takes the position that a DAO is not a smart contract or a
storage layout. Its honest meaning is the universal way to lift
anonymous local member choices to one global outcome along the
voter-orbit quotient. That is exactly the central object of the
[`unified-aggregation-theory`](https://github.com/MavenRain/unified-aggregation-theory)
(UAT) reservoir library, the left Kan extension of a choice rule along
the orbit projection:

```
⟦DAO⟧ = Aggregation act F = LeftKanExtension (orbitProjection act) F.
```

Every DAO concept is given a meaning by a total function `⟦·⟧` into this
single semantic domain, and the vocabulary is derived by requiring `⟦·⟧`
to be a homomorphism. Reusing `Aggregation` inherits, already
machine-checked, voter anonymity (the orbit quotient), legitimacy (the
Lan universal property), and the Arrow trichotomy of governance fates.

The full design is in **[`DENOTATIONAL-DESIGN.md`](DENOTATIONAL-DESIGN.md)**.
The formal encoding is the single file **`SelfReferentialDAO.lean`**.

## The three fates of self-governance

A DAO representation `(act, F)` lands in exactly one of UAT's three
regimes (`self_governance_trichotomy`, delegating to UAT `trichotomy`):

- **Arrow-Impossibility** (`¬ Nonempty (Aggregation act F)`): no
  legitimate anonymous aggregation exists, so governance is impossible.
  The clean exception-free reading is `govObj act F X = none`
  (`govObj_none_iff_impossible`). There is no self-constituting charter
  (`no_self_constitution`).
- **Arrow-Debreu** (object-unique Lan): a single legitimate verdict per
  configuration, consensus (`unique_self_constitution`).
- **Schelling-Ising** (object-distinct Lans, requiring the indiscrete
  phase target): two equally legitimate realized verdicts at some
  configuration, an object-fork (`constitutional_fork`).

The governance phase transition is tied to UAT's
`mean_field_bifurcation`: the cardinality of object-distinct
aggregations of `magChoiceRule n β` is the mean-field fixed-point count,
which bifurcates one to two at the critical coordination pressure
`β_c = 1` (`fork_transition`).

## Self-reference

Self-reference is the governance endo-operation on constitutions,
relative to a chosen aggregation `L`:

```
Gov (L : Aggregation act F) : ChoiceRule Obj D := orbitProjection act ⋙ L.functor
```

`Gov` restricts the global aggregate back to a local rule. A
self-referential DAO is a fixed point: `IsSelfConstituting F` says some
realization fixes `F` object-wise. The amendment operation has its
meaning forced as a genuine homomorphism, `⟦amend⟧ = Gov`
(`hom_amend` / `govPhi_canonical_eq_gov`, by `rfl`).

## Honest scope (read before citing)

Mirroring UAT's own "Scope, stated honestly":

- The self-reference / bifurcation correspondence holds at the level of
  **`Aggregation`-object-cardinality**, NOT at the level of the
  fixed-point predicate `IsSelfConstituting`. For the shipped constant
  constitution `magChoiceRule n β = constIndiscrete (zeroPhase β)`,
  `IsSelfConstituting` is single-valued at every `β` (always and only
  the zero phase: `canonical_self_constituting`,
  `nonzero_phase_not_fixpoint`, `self_constitution_unique_zero_phase`).
  A self-constitution that genuinely bifurcates would require a
  non-constant, order-parameter-pinning constitution. That is the prime
  extension and is not delivered here.
- Proposal functoriality (`gov_map_comp`) is type-correct but vacuous
  over the discrete shipped witnesses (only identity proposals). Genuine
  proposals need a non-discrete configuration category.
- The "instances are morphisms" slogan is retracted in writing: no
  algebraic type-class morphism law is exhibited. Treasury (needs a
  monoidal `D`), quorum (needs a subobject construct), and naturality of
  `F ↦ Aggregation act F` (needs a 2-categorical statement) are out of
  scope of the verified UAT surface.

## Status

Builds green against the real on-disk UAT API (`lake build
SelfReferentialDAO`, Lean v4.31.0), zero `sorry`, every proof in term
mode (so the kan-tactics-only-inside-`by` convention holds vacuously,
and no Mathlib tactic appears). The load-bearing theorems use only the
standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`);
the pure regime reductions use `propext` alone.

`AxCheck.lean` is a standalone axiom-audit helper: it `#print axioms` for
every load-bearing theorem. It is not part of the library target, so a
normal `lake build` does not build it.

## Building

```sh
lake build
```

This library depends on `unified-aggregation-theory` by git (`rev =
"main"`), so a fresh clone resolves the whole chain (comp-cat-theory and
kan-tactics arrive transitively) with no sibling checkout required. Pin
`rev` to a tag or commit instead of `main` for a reproducible build. To
develop against a local UAT checkout next door, swap the git require for:

```toml
[[require]]
name = "unified-aggregation-theory"
path = "../unified-aggregation-theory"
```

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
