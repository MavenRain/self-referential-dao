# Denotational Design for a UAT-Respecting Self-Referential DAO

## (a) Stance and method: denotational design in Lean 4

This document follows Conal Elliott's denotational design (the LambdaPix report "Denotational design with type class morphisms", plus the "denotation of the denotation" and "semantic editor combinators" writings). You do not start from a data structure and ask what it does; you start from what the thing IS mathematically (the Model / denotation), pick a Representation, and give a total meaning function `⟦.⟧ : Representation -> Model` that is the spec. Once the Model is fixed, each operation's meaning is forced: for `op` on the Representation there must be `op'` on the Model with `⟦ op a b ⟧ = op' ⟦a⟧ ⟦b⟧`, i.e. `⟦.⟧` is a homomorphism.

Honest correction to the prior draft: the previous version name-dropped "every operation is forced" and "instances are morphisms" without instantiating either. This revision practices the method only where it actually holds and RETRACTS the rest in writing.

- The one genuine operation-level homomorphism is amendment. `govPhi_canonical_eq_gov : GovPhi (canonicalAmendment act) L = Gov L` is exactly `⟦amend⟧ = Gov`, an equation relating an operation on representations (`GovPhi (canonicalAmendment act)`) to an operation on the model (`Gov`), holding by `rfl`. It is restated under the law name as `hom_amend`.
- The content-bearing half of `⟦.⟧` is functoriality of the induced constitution: `gov_map_comp : (Gov L).map (p ≫ q) = (Gov L).map p ≫ (Gov L).map q`. This is `Functor.map_comp` for the composite `Gov L`, so `⟦propose p ; q⟧ = ⟦propose q⟧ ∘ ⟦propose p⟧` is forced by `Gov L` being a functor. It is vacuous over a discrete `Obj` (only identity proposals) and content-bearing over any non-discrete configuration category; the prime extension remains a non-discrete `Obj`.
- "Instances are morphisms" is RETRACTED, not silently dropped. No algebraic type class on `DAORep` is given a structure-preserving `⟦.⟧`. The only candidates (treasury as a monoid object; naturality of `F ↦ Aggregation act F`) are out of scope of the verified UAT surface, so the slogan is not claimed.
- The remaining named laws (`hom_tally_anonymity`, `hom_legitimacy_unique`) are labelled in the file as RE-EXPORTS of model properties under DAO names, not as homomorphism laws. This is the honest description: they are category-theory facts (orbit-constancy, Lan uniqueness) given a DAO reading.

Three Lean-4 discipline points under MavenRain's conventions:
1. Meaning functions are `def`, the load-bearing facts are `theorem` (discharged proofs, not QuickCheck properties). That is the reason to port to Lean.
2. All proofs are TERM MODE (pattern-matching equations, `fun`, anonymous constructors, `.rec`, term-mode `match`). The file contains zero `by`-blocks, so the "kan-tactics only inside `by`" rule is satisfied vacuously and no Mathlib tactic appears.
3. Genuine partiality (the impossibility regime) is `Option`-valued via a dependent `if` (`dite`) reduced by `dif_pos` / `dif_neg`, never `panic!` / `throw`, never a `match` on `Option`, and no wildcard arm on a finite sum.

The accompanying file is `SelfReferentialDAO.lean` at the repo root (the lakefile `defaultTargets`), which `require`s `unified-aggregation-theory`. It builds green (`lake build SelfReferentialDAO`, 64 jobs), has zero `sorry`. Load-bearing theorems use `propext`, `Classical.choice`, `Quot.sound`; the pure regime reductions (`no_self_constitution`, `unique_self_constitution`, `constitutional_fork`, `gov_map_comp`, `hom_legitimacy_unique`, `hom_tally_anonymity`) use `propext` alone.

## (b) The semantic domain: UAT, and why `Aggregation` is the meaning of a DAO

UAT supplies the semantic domain. The Mathlib-free API the design rides on, verified against source:
- `Category.{u,v}`, `Functor` (`obj`, `map`, `map_id`, `map_comp`), `NatTrans` (`app`, `naturality`), `F ⋙ G` = "apply `F` first then `G`", `NatTrans.whiskerRight`.
- `LeftKanExtension K F` with fields `functor`, `unit : F ⟹ (K ⋙ functor)`, `desc`, `fac`, `uniq`, and `LeftKanExtension.desc_unique` (whose factorization hypotheses use `whiskerRight β K`).
- `SymmetryGroup.{u}`, `GAction G Obj` (`act_one`, contravariant `act_mul g h = act h ⋙ act g`).
- `ChoiceRule Obj D := Obj ⥤ D`; `BetaChoiceFamily`.
- `OrbitGroupoid act` (field `val : Obj`, `Type u`, carrying `Category.{u, max u w}`), `OrbitHom`, `orbitProjection act : Obj ⥤ OrbitGroupoid act`.
- `Aggregation act F := LeftKanExtension (orbitProjection act) F`. The central object.
- Regime predicates in `Regimes.lean` (object-equality form), `trichotomy`, `Indiscrete` with `indiscreteLan` existing at any object, `Characterization.lan_implies_orbit_constant` / `not_schelling_ising_discrete`, and the `Bridge.SchellingIsing` content (`IsMeanFieldFixedPoint`, `mean_field_bifurcation`, `MagPhase`, `magChoiceRule`, `zeroPhase`, `paramagnetic_arrow_debreu_regime`, `schelling_ising_regime`).

Universe claim, corrected (minor finding). `Aggregation` and `OrbitGroupoid` natively take `G : SymmetryGroup.{w}` FREELY, with `OrbitGroupoid act : Type u` and `OrbitHom : Type (max u w)`. Only `Regimes.lean`, `Characterization.lean`, `Trichotomy.lean` specialize to `{u}` with the group in the object universe. So the DAO fixing `w = u` in `DAORep` / `Gov` / etc. is a RESTRICTION of the underlying construction (chosen so the regime predicates apply verbatim), not a forced theorem. The file's section-1 doc-comment states this explicitly. It loses no DAO-relevant generality (one anonymity group, one config universe).

Why `Aggregation` is the meaning of a DAO. A DAO is not a smart contract or storage layout. The honest meaning is the universal way to lift anonymous local member choices to one global outcome along the voter-orbit quotient: a left Kan extension of the constitution `F` along `orbitProjection act`. Reusing `Aggregation` inherits voter anonymity (the orbit quotient), legitimacy (the Lan universal property), and the Arrow trichotomy, all already machine-checked.

## (c) The meaning function `⟦.⟧` and the semantic dictionary

The MODEL is `Aggregation act F`, a `Type` of left Kan extensions. The REPRESENTATION is `DAORep Obj G D`, packaging `act : GAction G Obj` and `constitution : ChoiceRule Obj D`. The meaning is `⟦ r ⟧ := Aggregation r.act r.constitution`, with the notation `⟦ r ⟧` in the file. The Representation mentions no storage slots, ballots-as-bytes, gas, or block height.

`Aggregation act F` is a `Type` (a structure of realizations), not a term. "The DAO as a running instance" is an inhabitant `L : Aggregation act F`. The governance question "does a legitimate aggregate exist / is it unique" is a property of the whole type. This forces the `L`-carrying `Gov` in section (e).

Semantic dictionary (DAO concept, UAT denotation, status):

| DAO concept | UAT denotation | status |
|---|---|---|
| member / voter | not an object; a coordinate acted on by `G` (`act_one`, `act_mul`); binary factions `Z2`, full anonymity a symmetric group | sound |
| configuration | an object of `Obj`, `[Category.{u,u} Obj]`; witnesses use `Discrete (SpinConfig n)` | sound |
| proposal (config update) | a `C`-morphism `p : Hom x y`; sequencing `≫`; functoriality forces `⟦propose p;q⟧ = ⟦q⟧ ∘ ⟦p⟧` (`gov_map_comp`) | type-correct, VACUOUS over the discrete witnesses (only identity morphisms); the prime extension point |
| ballot / preference | a coordinate of the config object; the `G`-action carrier (`Z2.actOnConfig`) | sound |
| vote (act of casting) | choosing a config object; anonymized content is its `orbitProjection` image | sound |
| constitution | `F : ChoiceRule Obj D`, a functor; family form `BetaChoiceFamily` | sound |
| anonymity | `G` plus `act` plus `orbitProjection act`; orbit-constancy is a THEOREM (`lan_implies_orbit_constant`), not an axiom | sound, proven |
| tally | `(L : Aggregation act F).functor.obj : OrbitGroupoid act -> D` | sound (a property of a chosen `L`) |
| decision / outcome | an object of `D`, `[Category.{v,v} D]`; for self-reference `D` carries phase data (`MagPhase β`) | sound |
| legitimacy | the Lan universal property (`unit`, `desc`, `fac`, `uniq`, `desc_unique`) | sound, proven |
| consensus | `IsArrowDebreuRegime act F` (object-unique Lan); witness `paramagnetic_arrow_debreu_regime` | sound, proven |
| object-fork / faction | `IsSchellingIsingRegime act F` (object-distinct Lans); needs `Indiscrete`; impossible over `Discrete` | sound, proven |
| governance-failure | `IsArrowImpossibilityRegime act F := ¬ Nonempty (Aggregation act F)` | sound, proven |
| amendment | `⟦amend⟧ = Gov` (`govPhi_canonical_eq_gov`, `hom_amend`) | sound |
| self-constitution | `IsSelfConstituting F := ∃ L, ∀ X, (Gov L).obj X = F.obj X` | sound; single-valued for the shipped constant constitution, see (e),(f) |
| quorum / threshold | a predicate `OrbitGroupoid act -> Prop` | aspirational; no subobject construct in the verified surface |
| treasury | a commutative monoid of balances | OUT OF SCOPE; no monoidal `D` in the verified API |

## (d) The vocabulary and its laws

- `gov_map_comp` : `(Gov L).map (p ≫ q) = (Gov L).map p ≫ (Gov L).map q` = `Functor.map_comp` for `Gov L`. The genuine content-bearing half of `⟦.⟧`. Honest caveat in its doc-comment: vacuous over discrete witnesses, content-bearing over a non-discrete `Obj`.
- `hom_amend` / `govPhi_canonical_eq_gov` : `GovPhi (canonicalAmendment act) L = Gov L` by `rfl`. The one genuine operation-level homomorphism, `⟦amend⟧ = Gov`.
- `hom_tally_anonymity` : `F.obj ((act.act g).obj x) = F.obj x`, labelled a RE-EXPORT of `lan_implies_orbit_constant` (model property), not a homomorphism law.
- `hom_legitimacy_unique` : labelled a RE-EXPORT of `LeftKanExtension.desc_unique` (model property), not a homomorphism law.
- `gov_obj` : `(Gov L).obj X = L.functor.obj { val := X }` by `rfl`, the definitional bridge to the regime predicates.

Two thesis claims explicitly NOT delivered: naturality of `F ↦ Aggregation act F` (needs a 2-categorical statement absent from the surface) and treasury monoid homomorphisms (need a monoidal `D`).

## (e) Self-reference: `Gov`, the fixpoint, `IsSelfConstituting`, `Φ`, and the honesty fix

Goal: a DAO whose outcomes can rewrite its own constitution, i.e. a fixed point of a governance endo-operation.

The corrected `Gov`. The naive `orbitProjection act ⋙ (Aggregation act F).functor` is ill-typed (`Aggregation act F` is a `Type`). The type-correct form carries a chosen realization `L`:
```
Gov (L : Aggregation act F) : ChoiceRule Obj D := orbitProjection act ⋙ L.functor
```
The dependence on `L` is the none / one / many structure the trichotomy classifies.

`Φ` and the canonical reflection. `AmendmentRule act := (OrbitGroupoid act ⥤ D) -> ChoiceRule Obj D`; `GovPhi Phi L := Phi L.functor`; `canonicalAmendment act := fun H => orbitProjection act ⋙ H`; `GovPhi (canonicalAmendment act) L = Gov L` definitionally.

The unit is the comparison. `govUnit L := L.unit : F ⟹ Gov L`, NOT new data (Lambek coalgebra framing). `fixpointEndo L (h : Gov L = F) : F ⟹ F` transports `govUnit L` along functor equality; it is provided for downstream consumers and `govUnit` is genuinely used inside it (no dead def). `GovRel F X d := ∃ L, (Gov L).obj X = d` is the multivalued side, wired by `govRel_of_aggregation L X : GovRel F X ((Gov L).obj X)` so it is not inert.

The fixpoint, at object granularity. `IsFixedPointObj L := ∀ X, (Gov L).obj X = F.obj X`. `IsSelfConstituting F := ∃ L, IsFixedPointObj L`. Existence-form, total `Prop`, false in Arrow-Impossibility (`no_self_constitution`).

THE CENTRAL HONESTY FIX (blocker). The prior draft claimed the fork produces "two equally legitimate self-constitutions `±m_*`". This is FALSE against the shipped constitution and is now corrected, with both directions proved:

- The shipped `magChoiceRule n β = constIndiscrete (zeroPhase β)` is CONSTANT: `F.obj X = zeroPhase β = ⟨⟨0, _⟩⟩` for every config `X` and every `β` (verified in source: `SchellingIsing.lean` L526-527). So `L` self-constitutes iff its chosen phase object is `zeroPhase β`.
- `canonical_self_constituting (n β) : IsSelfConstituting (magChoiceRule n β)` holds at EVERY `β` (including `β > 1`), witnessed by `zeroPhaseAggregation` (the `indiscreteLan` at `zeroPhase β`), whose fixpoint proof `zeroPhaseAggregation_isFixedPoint` closes by `fun _ => rfl`. The `β`-hypothesis is genuinely unused. So `IsSelfConstituting` does NOT bifurcate.
- `nonzero_phase_not_fixpoint (n) (hm : m ≠ 0) (hfix : IsMeanFieldFixedPoint β m) : ¬ IsFixedPointObj (indiscreteLan ... ⟨m, hfix⟩)`. The fork branch at `m ≠ 0` assigns `⟨⟨m, _⟩⟩ ≠ ⟨⟨0, _⟩⟩ = F.obj X` at the all-up config, refuted via `congrArg Subtype.val ∘ congrArg Indiscrete.val`. This is the precise refutation of "the fork branches are self-constitutions".
- `self_constitution_unique_zero_phase (n β) (L) (hself) : L.functor.obj { val := ⟨upConfig n⟩ } = zeroPhase β`. Any self-constituting realization assigns the zero phase at the all-up config: the self-constituting witness is single-valued at every `β`.

So `IsSelfConstituting` is single-valued for this constitution; the FORK lives in `Aggregation`-object-cardinality (section f), a strictly different quantity. Making `IsSelfConstituting` itself bifurcate would require a non-constant constitution that pins its order parameter (`F.obj X = ⟨m_*(X)⟩` so `Gov L = F` forces `m = r(βm)`); that is the prime extension and is NOT delivered. This limitation is stated in the file header, in the section-4 caution, and in the section-8 doc-comments.

Soundness (no Girard paradox, no size blowup). The constitution is DATA in a fixed small `D`, not an impredicative quantifier. `Φ : (OrbitGroupoid act ⥤ D) -> (Obj ⥤ D)` maps OUT of the functor category; no `D` contains its own function space. The canonical instance has `Obj = SpinConfigCat n : Type 0`, `D = MagPhase β : Type 0`, `G = Z2Group : SymmetryGroup.{0}`, so everything lives at `u = v = w = 0`, no `Type : Type`. `IsSelfConstituting` is `Prop`-valued and positive in `L`. Non-vacuity is real but TRIVIAL: the witness is always the zero phase, which is exactly why the predicate fails to discriminate the regimes (stated honestly).

## (f) The trichotomy as three fates, and the honest bifurcation correspondence

Reductions to the UAT regime predicates by definitional unfolding through `gov_obj`:
- `no_self_constitution : IsArrowImpossibilityRegime act F -> ¬ IsSelfConstituting F`. A genuine statement about `IsSelfConstituting`. (propext only.)
- `unique_self_constitution : IsArrowDebreuRegime act F -> ∃ L, ∀ L' X, (Gov L).obj X = (Gov L').obj X`. Object-uniqueness of the `Gov`-induced verdict (regime currency), NOT a fixed-point claim. Reduces by specializing the regime's `Y` to `⟨X⟩`. (propext only.)
- `constitutional_fork : IsSchellingIsingRegime act F -> ∃ L₁ L₂ X, (Gov L₁).obj X ≠ (Gov L₂).obj X`. Object-distinctness of two AGGREGATIONS (this IS `IsSchellingIsingRegime` with `Y` renamed to `⟨Y.val⟩`), NOT two self-constituting fixpoints. (propext only.)
- `self_governance_trichotomy` : delegates to `trichotomy`.

These three are honestly named in the file: `unique_self_constitution` and `constitutional_fork` are about object-uniqueness / object-distinctness of `Gov`, NOT about the fixed-point set. The relationship to the fixed-point set is made precise in section (e): for the shipped constitution the fixed-point set does NOT fork.

The bifurcation correspondence, stated honestly. `mean_field_bifurcation` computes the cardinality of the mean-field fixed-point set: 1 for `β ≤ 1` (only `m = 0`), at least 2 for `β > 1` (the pair `±(β-1)/β`). The objects of `MagPhase β = Indiscrete {m // IsMeanFieldFixedPoint β m}` ARE those fixed points, and `indiscreteLan` exists at any object, so the count of object-distinct aggregations of `magChoiceRule n β` equals that cardinality (`Indiscrete.mk_ne`). This is a real correspondence for `Aggregation`-OBJECT-cardinality. It is NOT a correspondence for `IsSelfConstituting` (which is single-valued). The bifurcation cardinality is IMPORTED from `mean_field_bifurcation` and re-labels indiscrete objects whose `Rat` label is inserted exogenously into a `PUnit`-hom groupoid; the categorical construction does not itself compute the self-consistency map (a faithful version would make `F` depend on its config so `Gov L = F` forces `m = r(βm)`). This major finding is acknowledged in the file header and section-8/9 doc-comments.

`fork_transition (n) (β)` packages:
```
(β ≤ 1 -> ∃ L, ∀ L' X, (Gov L).obj X = (Gov L').obj X)  ∧  (1 < β -> ∃ L₁ L₂ X, (Gov L₁).obj X ≠ (Gov L₂).obj X)
```
proved by `unique_self_constitution (paramagnetic_arrow_debreu_regime n hβ)` and `constitutional_fork (schelling_ising_regime n hβ)`. Both legs are the SAME `Aggregation` construction; `β_c = 1` is inherited verbatim. Its doc-comment states the second leg is two object-distinct AGGREGATIONS, not two fixpoints, and that `IsSelfConstituting` is single-valued at all `β`. Reinterpreting `β` as coordination pressure: below `β_c` the governance verdict is object-unique (consensus); above `β_c` two distinct legitimate verdicts `±m_*` appear (an object-fork of the realized aggregate).

## (g) What is proved versus assumed (honest scope)

Proved (machine-checked, zero `sorry`, kernel build green, axiom-checked):
- `Gov`, `GovPhi`, `canonicalAmendment`, `govUnit`, `fixpointEndo`, `IsFixedPointObj`, `IsSelfConstituting`, `GovRel`, `govObj` well-typed against the exact UAT signatures; `govUnit`/`fixpointEndo`/`GovRel` all wired into theorems (`fixpointEndo` uses `govUnit`; `govRel_of_aggregation` uses `GovRel`), no dead defs.
- `gov_obj`, `govPhi_canonical_eq_gov`, `hom_amend` by `rfl`.
- `gov_map_comp` = `Functor.map_comp` for `Gov L` (type-correct; vacuous over discrete witnesses, stated honestly).
- `govRel_of_aggregation`.
- `hom_tally_anonymity` re-exports `lan_implies_orbit_constant`; `hom_legitimacy_unique` re-exports `LeftKanExtension.desc_unique` (both labelled model properties).
- `govObj_none_iff_impossible` (both directions).
- `no_self_constitution`, `unique_self_constitution`, `constitutional_fork`, `self_governance_trichotomy`.
- `zeroPhaseAggregation`, `zeroPhaseAggregation_isFixedPoint`, `canonical_self_constituting` (holds at ALL β), `nonzero_phase_not_fixpoint`, `self_constitution_unique_zero_phase`: the four new theorems that make the self-reference layer honest and non-decorative.
- `fork_transition`, `canonical_aggregation_below_critical`, delegating to `paramagnetic_arrow_debreu_regime` / `schelling_ising_regime` (hence `mean_field_bifurcation`).
- Axiom profile: load-bearing theorems use `propext`, `Classical.choice`, `Quot.sound`; the pure regime reductions and the two re-exports and `gov_map_comp` use `propext` alone. No `sorryAx`.

Assumed or out of scope (honest, mirroring UAT's own scope):
- `IsSelfConstituting` does NOT bifurcate for the shipped constant constitution (single-valued at all β). A bifurcating self-constitution needs a non-constant order-parameter-pinning constitution. NOT delivered; the prime self-reference extension.
- Proposal functoriality (`gov_map_comp`) is vacuous over the discrete shipped witnesses; genuine proposals need a non-discrete `Obj`. The second-highest-value extension.
- "Instances are morphisms" RETRACTED: no type-class morphism law is exhibited.
- Naturality of `F ↦ Aggregation act F`, treasury monoid object, quorum sub-functor: out of scope (no 2-categorical / monoidal / subobject construct in the verified surface).
- Knaster-Tarski is not used; fixpoint existence is constructive via `zeroPhaseAggregation` / `mean_field_bifurcation`. Lambek's lemma is a theorem only over the indiscrete target and an analogy elsewhere (framing-only).
- The structure-eta reliance (`{ val := Y.val }` defeq `Y` for single-field `OrbitGroupoid`) is load-bearing and stable in Lean 4; noted.

## (h) Worked micro-example: a 2-member, Z2-symmetric DAO

Take `n = 2`, the `Z2` flip symmetry (`spinConfigAction 2` on `SpinConfigCat 2`), constitution `magChoiceRule 2 β` into `MagPhase β`. Both members are interchangeable: `Z2` flips both ballots simultaneously, so anonymity is the orbit quotient of the four configs under simultaneous flip.

Self-constitution, ALL `β`. `canonical_self_constituting 2 β : IsSelfConstituting (magChoiceRule 2 β)` holds at every `β`, witnessed by the zero-phase realization `zeroPhaseAggregation 2 β`. The DAO always admits a single self-legitimating charter: the symmetric phase `m = 0`. This is single-valued: `self_constitution_unique_zero_phase` shows any self-constituting realization assigns `zeroPhase β` at the all-up config.

Object-fork, `β > 1`. `bifurcation_ferromagnetic` gives the pair `±(β-1)/β`, two distinct objects of `MagPhase β`. `indiscreteLan` at each yields two aggregations whose object-assignments differ (`Indiscrete.mk_ne`), so `schelling_ising_regime 2 hβ`. Feeding this to `constitutional_fork` (second leg of `fork_transition 2 β`) produces `L₁, L₂, X` with `(Gov L₁).obj X ≠ (Gov L₂).obj X`: two object-distinct legitimate AGGREGATIONS `±m_*`. CRUCIALLY, by `nonzero_phase_not_fixpoint`, these are NOT self-constitutions of the constant `F`: they are object-distinct aggregates, not fixed points of `Gov` relative to `F`. The DAO's REALIZED aggregate forks; its SELF-CONSTITUTING charter does not (it stays the unique zero phase).

The transition is `fork_transition 2 β` at `β_c = 1`: the single construction `Aggregation (spinConfigAction 2) (magChoiceRule 2 β)` realizes object-uniqueness below the critical pressure and object-distinctness above it, and the cardinality jump 1 -> 2 of the object-assignment set is `mean_field_bifurcation` read through `D = MagPhase β`. The honest claim is that the GOVERNANCE PHASE TRANSITION IS AN OBJECT-FORK TRANSITION (of the realized aggregate), inheriting `β_c = 1` verbatim, while the self-constituting charter set is single-valued throughout.
