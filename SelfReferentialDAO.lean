/-
  SelfReferentialDAO

  A denotational design (Conal Elliott) for a self-referential DAO, with
  the semantic domain supplied by the UnifiedAggregation (UAT) categorical
  machinery.  This file is a reservoir library: downstream DAO projects
  `require` it and reuse the meaning function, the governance endo-operation
  `Gov`, the self-constitution predicate, and the three self-governance
  corollaries (no self-constitution / unique self-constitution / object-fork),
  all reduced to the UAT regime predicates.

  Central denotation:

    ⟦DAO⟧ = Aggregation act F = LeftKanExtension (orbitProjection act) F.

  A DAO is the universal way to lift anonymous local member choices `F`
  to one global outcome along the voter-orbit quotient `orbitProjection act`.

  Design conventions honored throughout:
  - Lean 4 only, no Mathlib dependency (builds on comp-cat-theory,
    kan-tactics, unified-aggregation-theory).
  - Inside every `by` block: kan-tactics only.  Classical case analysis,
    destructuring, and structure-field substitution are done in TERM MODE
    (pattern-matching equations, `fun`, anonymous constructors, `.rec`),
    which the convention permits.
  - No partiality leaks: genuine partiality is `Option`-valued (the
    impossibility regime), handled by combinators / a dependent `if`,
    never panic/throw, never a `match` on `Option`.
  - `set_option autoImplicit false`; structures/newtypes over primitives.
  - No em-dashes anywhere.

  Honest scope (read before citing): the headline correspondence between the
  governance phase transition and the mean-field bifurcation holds at the
  level of OBJECT-DISTINCT AGGREGATIONS (the regime currency), NOT at the
  level of the fixed-point predicate `IsSelfConstituting`.  For the shipped
  constant constitution `magChoiceRule n β = constIndiscrete (zeroPhase β)`,
  `IsSelfConstituting` is single-valued at every `β` (it is always satisfied
  by the zero-phase realization, and ONLY by it), so it does not bifurcate.
  The fork lives in the cardinality of `Aggregation`-object-assignments, and
  that cardinality is exactly the fixed-point set computed by
  `mean_field_bifurcation`.  Both claims are theorems below
  (`canonical_self_constituting`, `nonzero_phase_not_fixpoint`,
  `self_constitution_unique_zero_phase`, `fork_transition`).  Making
  `IsSelfConstituting` itself bifurcate would require a NON-constant
  constitution that genuinely pins its order parameter; that is flagged as
  the prime extension and is not delivered here.

  Status: builds green against the real API (lake build passes, zero
  `sorry`); the load-bearing theorems use only the standard classical
  axioms (propext, Classical.choice, Quot.sound), and the pure regime
  reductions use propext alone.  Downstream `lakefile.toml` should carry:

    [[require]]
    name = "unified-aggregation-theory"
    git  = "https://github.com/MavenRain/unified-aggregation-theory.git"
    rev  = "main"
-/

import KanTactics
import UnifiedAggregation.Aggregation
import UnifiedAggregation.Regimes
import UnifiedAggregation.Trichotomy
import UnifiedAggregation.Indiscrete
import UnifiedAggregation.Characterization
import UnifiedAggregation.Bridge.SchellingIsing

set_option autoImplicit false

universe u v w

namespace SelfReferentialDAO

open CompCatTheory
open CompCatTheory.Category
open CompCatTheory.Functor
open UnifiedAggregation
open UnifiedAggregation.Bridge

/-! ## 1. The meaning function `⟦·⟧`

The MODEL of a DAO is `Aggregation act F`, a `Type` of left Kan extensions.
A REPRESENTATION is a packaging of the data a DAO instance is built from
(the symmetry `G`, its action `act`, and the local constitution `F`).  The
meaning of a representation is the corresponding aggregation type.

Universe note (honest): `Aggregation` natively takes `G : SymmetryGroup.{w}`
freely, with `OrbitGroupoid act : Type u` and `OrbitHom : Type (max u w)`.
The UAT regime predicates and `trichotomy`, however, are stated at `{u}`
with the group in the object universe.  To reuse those predicates verbatim
the DAO RESTRICTS the group universe to `w = u`.  This is a design choice
that loses no DAO-relevant generality (one anonymity group, one config
universe), not a forced theorem; the underlying `Aggregation` construction
is strictly more general. -/

/-- The REPRESENTATION of a DAO: the anonymizing symmetry action together
with the local-to-local constitution.  These are exactly the inputs the
central `Aggregation` construction consumes; nothing about storage,
ballots-as-bytes, gas, or block height appears here. -/
structure DAORep
    (Obj : Type u) [Category.{u, u} Obj]
    (G : SymmetryGroup.{u}) (D : Type v) [Category.{v, v} D] where
  /-- The anonymity action: how the relabeling group `G` permutes members.
  Anonymity is denoted by this action, and becomes a THEOREM about `⟦·⟧`
  via `lan_implies_orbit_constant`, not an extra axiom. -/
  act : GAction G Obj
  /-- The constitution: the local-to-local rule `if config is x, the
  locally correct outcome is F.obj x`. -/
  constitution : ChoiceRule Obj D

/-- The MEANING of a DAO representation: the `Type` of aggregations, i.e.
the type of left Kan extensions of the constitution along the voter-orbit
projection.  Total (every representation has a meaning-type); partiality of
*realization* lives one level down, as inhabitation of this type. -/
abbrev meaning
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {D : Type v} [Category.{v, v} D]
    (r : DAORep Obj G D) : Type _ :=
  Aggregation r.act r.constitution

@[inherit_doc] notation "⟦" r "⟧" => meaning r

/-! ## 2. The governance endo-operation `Gov`

`Gov` restricts a chosen global aggregate `L` back to a local rule: read a
config, project to its voter-orbit, report the global verdict there.  The
naive `orbitProjection act ⋙ (Aggregation act F).functor` is ILL-TYPED
(`Aggregation act F` is a `Type`, it has no `.functor` projection).  The
type-correct form carries the chosen realization `L` explicitly; that
dependence on `L` is precisely the none / one / many structure the
trichotomy classifies, not a wart. -/

/-- The governance endo-operation on constitutions, relative to a chosen
aggregation `L`.  `orbitProjection act : Obj ⥤ OrbitGroupoid act` and
`L.functor : OrbitGroupoid act ⥤ D`, so the composite (apply
`orbitProjection` first, then `L.functor`) is a `ChoiceRule Obj D`. -/
def Gov
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F) : ChoiceRule Obj D :=
  orbitProjection act ⋙ L.functor

/-- An amendment functor: any way of reading a global selector
`OrbitGroupoid act ⥤ D` back as a local constitution `Obj ⥤ D`.  The
canonical reflection is precomposition with `orbitProjection act` (pure
self-consistency); a general `Φ` models a self-rewriting constitution. -/
abbrev AmendmentRule
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D] : Type _ :=
  (OrbitGroupoid act ⥤ D) → ChoiceRule Obj D

/-- The canonical amendment rule: precomposition with the orbit projection.
`GovPhi canonicalAmendment L = Gov L` by definition. -/
def canonicalAmendment
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D] :
    AmendmentRule act (D := D) :=
  fun H => orbitProjection act ⋙ H

/-- The `Φ`-twisted governance operation. -/
def GovPhi
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    (Phi : AmendmentRule act (D := D))
    {F : ChoiceRule Obj D} (L : Aggregation act F) : ChoiceRule Obj D :=
  Phi L.functor

/-- The canonical `Φ` recovers `Gov` definitionally: pure self-consistency
is precomposition with the quotient.  This is the one genuine
operation-level homomorphism in the Conal sense: `⟦amend⟧ = Gov` holds by
`rfl`, an equation relating the amendment operation on representations to
the governance operation on the model. -/
theorem govPhi_canonical_eq_gov
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F) :
    GovPhi (canonicalAmendment act) L = Gov L := rfl

/-- `(Gov L)` evaluated at a config `X` is the global verdict at `X`'s
orbit, `L.functor.obj ⟨X⟩`.  This is the bridge between `Gov`-indexed-by
`Obj` and the regime predicates indexed by `OrbitGroupoid act`. -/
theorem gov_obj
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F) (X : Obj) :
    (Gov L).obj X = L.functor.obj { val := X } := rfl

/-- `(Gov L)` on a *proposal* (a config-morphism) is `L.functor` applied to
the orbit image of the proposal.  This is the genuinely content-bearing
half of the meaning function: it is `Functor.map_comp` for the composite
functor `Gov L`, so `⟦propose p ; q⟧ = ⟦propose q⟧ ∘ ⟦propose p⟧` is FORCED
by `Gov L` being a functor.  Vacuous over a discrete `Obj` (only identity
proposals); content-bearing over any non-discrete configuration category. -/
theorem gov_map_comp
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F)
    {X Y Z : Obj} (p : Hom X Y) (q : Hom Y Z) :
    (Gov L).map (p ≫ q) = (Gov L).map p ≫ (Gov L).map q :=
  (Gov L).map_comp p q

/-! ## 3. The canonical comparison and the unit at a fixpoint

The comparison natural transformation `η : F ⟹ Gov L` is NOT new data: it
is exactly the Lan unit `L.unit : F ⟹ (orbitProjection act ⋙ L.functor)`.
This is the coalgebra structure (Lambek framing): a self-constituting `F`
is one where this structure map becomes an endomorphism. -/

/-- The canonical comparison `η : F ⟹ Gov L` is the Lan unit, definitionally.
Used by `fixpointEndo` (the functor-level strengthening) and named so that
downstream consumers can speak of the coalgebra structure map directly. -/
def govUnit
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F) : F ⟹ Gov L :=
  L.unit

/-- At a *functor-level* fixpoint `Gov L = F`, transport the canonical unit
to an endo-natural-transformation `F ⟹ F`.  Functor equality is stronger
than the object-equality the regimes read; over the indiscrete phase target
it is automatic (every `map`-HEq is free), and that is the only place the
object-fork lives, so this form is available exactly where it is wanted.
Provided for downstream consumers that establish a functor-level fixpoint;
not instantiated by a concrete witness here (the shipped target is
indiscrete, where functor equality would be free but is not load-bearing). -/
def fixpointEndo
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F)
    (h : Gov L = F) : F ⟹ F :=
  -- Rewrite only the codomain `Gov L` to `F` in `govUnit L : F ⟹ Gov L`.
  -- `▸` cannot infer this higher-order motive, so transport explicitly.
  @Eq.mp (F ⟹ Gov L) (F ⟹ F) (congrArg (NatTrans F) h) (govUnit L)

/-! ## 4. The fixed point and `IsSelfConstituting`

Three notions of fixpoint were possible: functor equality (too strong, and
not what the predicates see), object equality (the regime currency), and
natural isomorphism (vacuous over the indiscrete target, where every
parallel pair is iso).  We use OBJECT equality.  `IsFixedPointObj L` then
says the local rule `Gov L` agrees object-wise with the constitution `F`.

CAUTION (load-bearing honesty, see the file header): for the shipped
constant constitution `IsFixedPointObj` is satisfied by exactly one
realization (the zero phase) at every `β`, so `IsSelfConstituting` does NOT
bifurcate.  The object-fork (`constitutional_fork`) is a statement about
`Aggregation`-object-assignments, which is strictly weaker than (and
disjoint in content from) self-constitution for this constitution. -/

/-- `L` self-constitutes at the object level: the local rule it induces by
self-aggregation agrees, object-wise, with the constitution `F` it came
from.  Since `(Gov L).obj X = L.functor.obj ⟨X⟩`, this is the object-level
content witnessed by the Lan unit precisely when `L.functor.obj ⟨X⟩` lands
back on `F.obj X`. -/
def IsFixedPointObj
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F) : Prop :=
  ∀ X : Obj, (Gov L).obj X = F.obj X

/-- A self-referential DAO: a constitution `F` admitting an aggregation `L`
that self-constitutes.  Existence-form, so it is a total `Prop` with no
partiality in its type.  It is FALSE in Arrow-Impossibility (no aggregation
at all).  It is TRUE whenever some realization fixes `F` object-wise; for
the shipped constant constitution that realization is the zero phase, and it
is the UNIQUE one (`self_constitution_unique_zero_phase`), at every regime.
The *cardinality* of object-distinct aggregations, which is what forks, is a
SEPARATE quantity read off the regime, not from this predicate. -/
def IsSelfConstituting
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ∃ L : Aggregation act F, IsFixedPointObj (act := act) L

/-- The relational graph of governance: `d` is *a* legitimate verdict at
`X`.  This is the multivalued side (it stays a `Prop`, never collapsed to a
value), so an object-fork is genuine non-uniqueness of the realized verdict,
not an exception.  Used by `govRel_of_aggregation` to connect a chosen `L`
to its graph. -/
def GovRel
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) (X : Obj) (d : D) : Prop :=
  ∃ L : Aggregation act F, (Gov L).obj X = d

/-- Every chosen aggregation populates the governance graph at its own
verdict.  Wires `GovRel` to concrete realizations so the relational side is
not inert. -/
theorem govRel_of_aggregation
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F) (X : Obj) :
    GovRel (act := act) F X ((Gov L).obj X) :=
  ⟨L, rfl⟩

/-! ## 5. The partial value interface `govObj`

Genuine partiality (the Arrow-Impossibility regime, where no aggregation
exists) is encoded with `Option`, never an exception.  `Option` not
`Except`: impossibility carries no informative error payload, it is a single
uninformative absence, so `Option` is the right shape.  `Classical.choice`
selects an aggregation when one exists; in the Arrow-Debreu regime the
choice is irrelevant (object-unique).  We branch with a dependent `if`
(`dite`) reduced by `dif_pos` / `dif_neg`, never a `match` on an `Option`. -/

/-- The governance partial value at a config `X`: `some d` when some
aggregation exists and assigns verdict `d` to `X`'s orbit, and `none`
exactly in the Arrow-Impossibility regime.  No `match` on `Option`, no
exception: the `none` branch is the clean denotation of impossibility. -/
noncomputable def govObj
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) (X : Obj) : Option D :=
  open Classical in
  if h : Nonempty (Aggregation act F)
    then some ((Gov (Classical.choice h)).obj X)
    else none

/-- In the Arrow-Impossibility regime `govObj` is `none`.  Uses `dif_neg`
on the defining `dite` keyed by the impossibility hypothesis. -/
theorem govObj_eq_none_of_impossible
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) (X : Obj)
    (himp : IsArrowImpossibilityRegime act F) :
    govObj act F X = none :=
  dif_neg himp

/-- Conversely, if `govObj` is `none` then we are in the Arrow-Impossibility
regime: were an aggregation to exist, the positive `dite` branch would give
`some _`, contradicting `none` by `Option.some_ne_none`. -/
theorem impossible_of_govObj_eq_none
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) (X : Obj)
    (hnone : govObj act F X = none) :
    IsArrowImpossibilityRegime act F :=
  fun hne =>
    Option.some_ne_none ((Gov (Classical.choice hne)).obj X)
      (Eq.trans
        (Eq.symm (show govObj act F X = some ((Gov (Classical.choice hne)).obj X)
                    from dif_pos hne))
        hnone)

/-- `govObj` returns `none` exactly in the Arrow-Impossibility regime.  The
clean, exception-free reading of "no anonymous Pareto+IIA rule exists, so
governance is impossible." -/
theorem govObj_none_iff_impossible
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) (X : Obj) :
    govObj act F X = none ↔ IsArrowImpossibilityRegime act F :=
  Iff.intro
    (impossible_of_govObj_eq_none act F X)
    (govObj_eq_none_of_impossible act F X)

/-! ## 6. Homomorphism laws and re-exported regime facts (Conal discipline)

Honest framing.  Conal's "the meaning of every operation is FORCED by
`⟦op a b⟧ = op' ⟦a⟧ ⟦b⟧`" is carried out for the ONE genuine operation this
design defines on representations: amendment.  `govPhi_canonical_eq_gov`
(section 2) is exactly `⟦amend⟧ = Gov`, an equation relating an operation on
representations to an operation on the model, by `rfl`.

We do NOT claim the broader "instances are morphisms" slogan: no algebraic
type class (Monoid, Functor, ...) on `DAORep` is given a structure-preserving
`⟦·⟧`.  The two natural candidates are out of scope (treasury needs a
monoidal `D`; naturality of `F ↦ Aggregation act F` needs a 2-categorical
statement absent from the verified surface), so the slogan is RETRACTED, not
quietly dropped.  The remaining laws below are: (a) `gov_map_comp`
(functoriality of the induced constitution, the content-bearing half of
`⟦·⟧`), and (b) re-exports of UAT facts under DAO names, each labelled as a
re-export of a model property rather than a homomorphism. -/

/-- RE-EXPORT (model property, not a homomorphism law).  Anonymity:
`⟦tally⟧` respects member relabeling, as a THEOREM not an axiom.  Existence
of the aggregation (a Lan along the orbit projection) forces the rule to
take equal values on `x` and `act g x`.  Delegates to the UAT theorem
`lan_implies_orbit_constant` (stated over a discrete outcome target). -/
theorem hom_tally_anonymity
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj} {α : Type u}
    (F : ChoiceRule Obj (Discrete α))
    (L : Aggregation act F) (g : G.carrier) (x : Obj) :
    F.obj ((act.act g).obj x) = F.obj x :=
  lan_implies_orbit_constant F L g x

/-- `⟦amend⟧ = Gov`: the amendment operation's meaning is the governance
endo-operation.  Stated as the definitional identity
`GovPhi canonicalAmendment = Gov`.  This is the genuine operation-level
homomorphism (a restatement of `govPhi_canonical_eq_gov` under the law name). -/
theorem hom_amend
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F) :
    GovPhi (canonicalAmendment act) L = Gov L := rfl

/-- RE-EXPORT (model property, not a homomorphism law).  Legitimacy as the
universal property: every local verdict factors through the global one,
uniquely.  Delegates to `LeftKanExtension.desc_unique`: any two mediating
transformations agreeing on the unit-factorization agree everywhere. -/
theorem hom_legitimacy_unique
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D} (L : Aggregation act F)
    {H : OrbitGroupoid act ⥤ D}
    (α : F ⟹ (orbitProjection act ⋙ H))
    (β₁ β₂ : L.functor ⟹ H)
    (h₁ : ∀ X, L.unit.app X ≫ (NatTrans.whiskerRight β₁ (orbitProjection act)).app X = α.app X)
    (h₂ : ∀ X, L.unit.app X ≫ (NatTrans.whiskerRight β₂ (orbitProjection act)).app X = α.app X)
    (Y : OrbitGroupoid act) :
    β₁.app Y = β₂.app Y :=
  LeftKanExtension.desc_unique L α β₁ β₂ h₁ h₂ Y

/-! ## 7. The three fates of self-governance, reduced to UAT regimes

Each corollary unfolds, through `gov_obj` (`(Gov L).obj X = L.functor.obj
⟨X⟩`), to the corresponding regime predicate.  No regime fact is re-proved.

These three are honestly named for what they are: `no_self_constitution` is
a genuine statement about `IsSelfConstituting`; `unique_self_constitution`
and `constitutional_fork` are statements about object-uniqueness /
object-distinctness of `Gov`-induced verdicts (the regime currency), NOT
about the fixed-point set.  The relationship between the object-fork and the
fixed-point set is made precise in section 8 (it does NOT fork). -/

/-- (i) NO SELF-CONSTITUTION.  In the Arrow-Impossibility regime there is no
aggregation at all, so no self-constituting `L`.  Governance is impossible.
A genuine statement about `IsSelfConstituting`. -/
theorem no_self_constitution
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D}
    (h : IsArrowImpossibilityRegime act F) :
    ¬ IsSelfConstituting (act := act) F :=
  fun ⟨L, _⟩ => h ⟨L⟩

/-- (ii) OBJECT-UNIQUE GOVERNANCE (consensus).  In the Arrow-Debreu regime an
aggregation exists and is object-unique, so any two governance-induced local
rules agree object-wise: a single legitimate verdict per config.  Reduces to
the regime's own `∀ L', ∀ Y, L.functor.obj Y = L'.functor.obj Y` by
specializing `Y` to `⟨X⟩`.  (Statement about object-uniqueness of `Gov`, not
about the fixed-point set.) -/
theorem unique_self_constitution
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D}
    (h : IsArrowDebreuRegime act F) :
    ∃ L : Aggregation act F,
      ∀ L' : Aggregation act F, ∀ X : Obj, (Gov L).obj X = (Gov L').obj X :=
  match h with
  | ⟨L, huniq⟩ => ⟨L, fun L' X => huniq L' { val := X }⟩

/-- (iii) CONSTITUTIONAL OBJECT-FORK.  In the Schelling-Ising regime two
aggregations disagree on an object, i.e. two distinct legitimate verdicts at
some config.  Reduces to the regime predicate by taking the witnessing orbit
object `Y` and reading it as `⟨Y.val⟩`.

This is non-uniqueness of the AGGREGATION (its object-assignment), which is
exactly `IsSchellingIsingRegime` with `Y` renamed.  It is NOT a claim that
`L₁, L₂` are two self-constituting fixpoints; for the shipped constitution
they are not (see `nonzero_phase_not_fixpoint`). -/
theorem constitutional_fork
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D}
    (h : IsSchellingIsingRegime act F) :
    ∃ L₁ L₂ : Aggregation act F, ∃ X : Obj, (Gov L₁).obj X ≠ (Gov L₂).obj X :=
  match h with
  | ⟨L₁, L₂, Y, hne⟩ => ⟨L₁, L₂, Y.val, hne⟩

/-- Trichotomy of self-governance: every DAO representation is in exactly one
of the three fates.  Delegates to the UAT `trichotomy`. -/
theorem self_governance_trichotomy
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) :
    IsArrowDebreuRegime act F ∨
    IsArrowImpossibilityRegime act F ∨
    IsSchellingIsingRegime act F :=
  trichotomy act F

/-! ## 8. Self-constitution of the canonical witness, and the honest
correspondence with `mean_field_bifurcation`

This section states EXACTLY what self-constitution does and does not do for
the shipped constant constitution `magChoiceRule n β = constIndiscrete
(zeroPhase β)`.  Two facts, both proved:

  (A) `IsSelfConstituting (magChoiceRule n β)` holds at EVERY `β`, witnessed
      by the zero-phase realization, and that realization is the ONLY one
      (object-wise) that self-constitutes.  So `IsSelfConstituting` is
      single-valued and does NOT bifurcate.

  (B) The object-distinct aggregations of the SAME constitution DO bifurcate
      1 → 2 at `β_c = 1` (`fork_transition`), and their count equals the
      mean-field fixed-point set.  This is the genuine correspondence, and it
      is a statement about `Aggregation`-object-cardinality, NOT about the
      fixed-point predicate.

The constant constitution sends every config to the reference phase
`zeroPhase β = ⟨0⟩`.  A realization `L` self-constitutes iff its chosen
phase object is `zeroPhase β`.  The fork branches sit at `±m_*`, which for
`m_* ≠ 0` are object-distinct from `F.obj X = ⟨0⟩`, hence NOT fixpoints.
Making `IsSelfConstituting` itself fork would require a non-constant
constitution that pins its order parameter (so `F.obj X = ⟨m_*(X)⟩`); that
is the prime extension and is not delivered here. -/

/-- The zero-phase realization of the canonical constitution: the
`indiscreteLan` at `zeroPhase β`.  Its functor is `constIndiscrete
(zeroPhase β) = magChoiceRule n β`, so it lands back on the constitution. -/
noncomputable def zeroPhaseAggregation (n : Nat) (β : Rat) :
    Aggregation (spinConfigAction n) (magChoiceRule n β) :=
  indiscreteLan (orbitProjection (spinConfigAction n)) (magChoiceRule n β)
    (zeroPhase β)

/-- The zero-phase realization self-constitutes at every `β`: `(Gov L).obj X
= L.functor.obj ⟨X⟩ = zeroPhase β = (magChoiceRule n β).obj X`, all four by
`rfl` (the `indiscreteLan` functor and `magChoiceRule` are both
`constIndiscrete (zeroPhase β)`).  The `β`-hypothesis is genuinely unused:
this holds in every regime. -/
theorem zeroPhaseAggregation_isFixedPoint (n : Nat) (β : Rat) :
    IsFixedPointObj (act := spinConfigAction n) (zeroPhaseAggregation n β) :=
  fun _ => rfl

/-- (A, existence half) The canonical self-referential DAO IS
self-constituting, at EVERY `β` (consensus AND above the critical pressure),
via the zero-phase realization.  This is single-valued: `IsSelfConstituting`
does not bifurcate.  Contrast `fork_transition`, where the OBJECT-distinct
aggregations bifurcate. -/
theorem canonical_self_constituting (n : Nat) (β : Rat) :
    IsSelfConstituting (act := spinConfigAction n) (magChoiceRule n β) :=
  ⟨zeroPhaseAggregation n β, zeroPhaseAggregation_isFixedPoint n β⟩

/-- (A, uniqueness half) A nonzero phase is NOT a fixpoint of governance for
the constant constitution.  If `m ≠ 0` is a mean-field fixed point, the
`indiscreteLan` at `⟨m⟩` assigns verdict `⟨m⟩ ≠ ⟨0⟩ = F.obj X` at the
all-up config, so `IsFixedPointObj` fails.  This is the precise refutation
of "±m_* are two self-constitutions": they are object-distinct aggregations,
not fixpoints.

Proof: instantiate `IsFixedPointObj` at `X = upConfig n`.  `(Gov L).obj X`
is `⟨⟨m, hm⟩⟩` and `F.obj X` is `zeroPhase β = ⟨⟨0, _⟩⟩`, both by `rfl`; the
two `Indiscrete` objects are unequal because `m ≠ 0` lifts through
`Subtype.val` and `Indiscrete.val`. -/
theorem nonzero_phase_not_fixpoint (n : Nat) {β m : Rat}
    (hm : m ≠ 0) (hfix : IsMeanFieldFixedPoint β m) :
    ¬ IsFixedPointObj (act := spinConfigAction n)
        (indiscreteLan (orbitProjection (spinConfigAction n))
          (magChoiceRule n β) (Indiscrete.mk ⟨m, hfix⟩)) :=
  fun hself =>
    hm (congrArg Subtype.val
      (congrArg Indiscrete.val (hself (Discrete.mk (upConfig n)))))

/-- (A, summary) For the shipped constant constitution, the ONLY object-wise
verdict that self-constitutes is the zero phase: any self-constituting
realization assigns `zeroPhase β` at the all-up config.  Hence
`IsSelfConstituting` carries a single witness class at every `β` and cannot
bifurcate; the fork lives entirely in `Aggregation`-object-cardinality. -/
theorem self_constitution_unique_zero_phase (n : Nat) (β : Rat)
    (L : Aggregation (spinConfigAction n) (magChoiceRule n β))
    (hself : IsFixedPointObj (act := spinConfigAction n) L) :
    L.functor.obj { val := Discrete.mk (upConfig n) } = zeroPhase β :=
  hself (Discrete.mk (upConfig n))

/-! ## 9. The fork transition, tied to `mean_field_bifurcation`

Instantiated at the canonical target `D = MagPhase β`, `Obj = SpinConfigCat
n`, `act = spinConfigAction n`, `F = magChoiceRule n β`, the OBJECT-FORK is
the two ends of the mean-field pitchfork at `β_c = 1`.  Both legs are the
SAME `Aggregation` construction; the existence proofs are reused verbatim
from UAT.  This is the (B) correspondence of section 8: it is about
object-distinct aggregations, NOT about the fixed-point set (which does not
fork, by section 8 (A)). -/

/-- THE GOVERNANCE PHASE TRANSITION IS AN OBJECT-FORK TRANSITION.  Below the
critical coordination pressure (`β ≤ 1`) the DAO's governance verdict is
object-unique (consensus); above it (`β > 1`) two distinct legitimate
verdicts `±m_*` appear at some config (a fork in the realized aggregate).
`β_c = 1` is inherited verbatim from `mean_field_bifurcation` via the UAT
regime witnesses `paramagnetic_arrow_debreu_regime` and
`schelling_ising_regime`.

HONEST READING: the second leg asserts `(Gov L₁).obj X ≠ (Gov L₂).obj X`,
i.e. two object-distinct AGGREGATIONS, NOT two self-constituting fixpoints
(see `nonzero_phase_not_fixpoint`).  `IsSelfConstituting` itself is
single-valued at all `β` (`canonical_self_constituting`); the bifurcation is
in the cardinality of `Aggregation` object-assignments, which equals the
mean-field fixed-point set. -/
theorem fork_transition (n : Nat) (β : Rat) :
    (β ≤ 1 →
       ∃ L : Aggregation (spinConfigAction n) (magChoiceRule n β),
         ∀ L' : Aggregation (spinConfigAction n) (magChoiceRule n β),
           ∀ X : SpinConfigCat n, (Gov L).obj X = (Gov L').obj X) ∧
    (1 < β →
       ∃ L₁ L₂ : Aggregation (spinConfigAction n) (magChoiceRule n β),
         ∃ X : SpinConfigCat n, (Gov L₁).obj X ≠ (Gov L₂).obj X) :=
  ⟨fun hβ => unique_self_constitution (paramagnetic_arrow_debreu_regime n hβ),
   fun hβ => constitutional_fork (schelling_ising_regime n hβ)⟩

/-- Existence corollary: below `β_c` the canonical self-referential DAO has
an aggregation (the `indiscreteLan` at the unique paramagnetic phase).
Strictly weaker than `canonical_self_constituting`, kept for the regime
audit trail. -/
theorem canonical_aggregation_below_critical (n : Nat) {β : Rat} (hβ : β ≤ 1) :
    Nonempty (Aggregation (spinConfigAction n) (magChoiceRule n β)) :=
  match paramagnetic_arrow_debreu_regime n hβ with
  | ⟨L, _⟩ => ⟨L⟩

end SelfReferentialDAO
