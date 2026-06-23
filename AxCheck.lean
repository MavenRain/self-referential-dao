import SelfReferentialDAO

open SelfReferentialDAO

-- axiom profiles of the load-bearing theorems
#print axioms govObj_none_iff_impossible
#print axioms fork_transition
#print axioms self_governance_trichotomy
#print axioms no_self_constitution
#print axioms unique_self_constitution
#print axioms constitutional_fork
#print axioms canonical_self_constituting
#print axioms nonzero_phase_not_fixpoint
#print axioms zeroPhaseAggregation_isFixedPoint
#print axioms self_constitution_unique_zero_phase
#print axioms gov_map_comp
#print axioms hom_legitimacy_unique
#print axioms hom_tally_anonymity

-- q-state Potts generalization (section 10): same regime currency, q-ary action
#print axioms potts_canonical_self_constituting
#print axioms pottsUniformAggregation_isFixedPoint
#print axioms potts_nonzero_phase_not_fixpoint
#print axioms potts_self_constitution_unique_uniform_phase
#print axioms potts_no_self_constitution
#print axioms potts_fork_transition
#print axioms potts_canonical_aggregation_below_critical

-- sanity: the two facts that make the honesty fix real
#check @nonzero_phase_not_fixpoint
#check @canonical_self_constituting

-- sanity: the q-ary honesty facts
#check @potts_nonzero_phase_not_fixpoint
#check @potts_canonical_self_constituting
