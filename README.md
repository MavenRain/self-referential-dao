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

## Multi-candidate governance (the q-state Potts generalization)

The binary witness above is the `Z2` faction flip. UAT's `Bridge.Potts`
generalizes it to a `q`-ary Potts spin under the full permutation symmetry
`S_q` on the colours, reusing the categorical core verbatim. Reading the
`q` colours as `q` interchangeable candidate choices, this is the same DAO
with `q` options instead of two factions, and section 10 of
`SelfReferentialDAO.lean` re-runs the entire self-governance narrative on
it (delegating to UAT's `potts_disordered_arrow_debreu_regime`,
`potts_ordered_schelling_ising_regime`, and `potts_arrow_impossibility_regime`):

- `potts_canonical_self_constituting`: the multi-candidate DAO
  self-constitutes at every `β`, via the disordered phase, single-valued.
- `potts_nonzero_phase_not_fixpoint`: an ordered phase (one dominant
  colour) is NOT a self-constitution, the q-ary honesty fix.
- `potts_no_self_constitution`: a non-anonymous q-ary rule has no
  self-constituting charter (Arrow-Impossibility).
- `potts_fork_transition`: object-unique below `β_c = 1`, object-forked
  above it, `β_c` inherited verbatim.

The new q-ary content is that above `β_c` the ordered phases form an
`S_q`-orbit of size `q` (one dominant colour each), so the realized-aggregate
fork is q-fold rather than the binary `±m_*` pair. What is PROVED, though, is
only the regime currency: at least two object-distinct verdicts (the colour-0
versus colour-1 pair, via `constitutional_fork`). The full q-fold
multiplicity as a theorem is flagged as the next UAT-side lemma, not claimed
here. The honest scope is otherwise unchanged: `IsSelfConstituting` stays
single-valued (the disordered phase), and the fork lives in
`Aggregation`-object-cardinality, exactly as in the binary case.

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
the pure regime reductions use `propext` alone (the q-ary
`potts_no_self_constitution` adds `Quot.sound`, from the `S_q`
orbit-quotient witness it supplies).

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
