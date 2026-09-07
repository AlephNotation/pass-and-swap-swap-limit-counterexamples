import OddCycle.Conclusions
import OddCycle.GeneralClosure
import OddCycle.GeneralHeight
import OddCycle.GeneralCommunication
import OddCycle.GeneralCardinality
import OddCycle.TwoFlowCompleteness
import OddCycle.FlowWordLabels
import OddCycle.TwoFlowBalance
import OddCycle.UniformObstruction
import OddCycle.BalancedRecurrence

/-! Print the trusted axioms used by the principal claims. Computational
certificates use kernel reduction. No native evaluation axiom is needed. -/

#print axioms OddCycle.mem_allStates_iff
#print axioms OddCycle.transition_valid
#print axioms OddCycle.carry_edgeEquiv_erase
#print axioms OddCycle.balanced_exchange
#print axioms OddCycle.balanced_transition
#print axioms OddCycle.balanced_events_closed
#print axioms OddCycle.balanced_region_nonempty_closed
#print axioms OddCycle.balanced_height
#print axioms OddCycle.reachable_of_orientation_eq
#print axioms OddCycle.branch_head_transition
#print axioms OddCycle.balanced_communication
#print axioms OddCycle.balanced_reachable_closed
#print axioms OddCycle.balanced_positive_rate_communication
#print axioms OddCycle.FiveJob.mem_support_iff
#print axioms OddCycle.FiveJob.support_height
#print axioms OddCycle.FiveJob.support_closed
#print axioms OddCycle.FiveJob.rate_positive
#print axioms OddCycle.FiveJob.head_communication
#print axioms OddCycle.FiveJob.canonical_defect
#print axioms OddCycle.FiveJob.canonical_scaled_not_stationary
#print axioms OddCycle.FiveJob.certificate_stationary
#print axioms OddCycle.FiveJob.probability_positive
#print axioms OddCycle.FiveJob.probability_sum
#print axioms OddCycle.FiveJob.probability_stationary
#print axioms OddCycle.FiveJob.probability_not_product
#print axioms OddCycle.FiveJob.proper_three_coloring
#print axioms OddCycle.FiveJob.normalized_certificate_not_product

#print axioms OddCycle.balanced_cardinality

#print axioms OddCycle.balanced_changed_event_head
#print axioms OddCycle.balanced_changed_head_injective
#print axioms OddCycle.two_flow_completeness

#print axioms OddCycle.flowWordX_labels
#print axioms OddCycle.flowWordY_labels
#print axioms OddCycle.flowQueue_labels
#print axioms OddCycle.two_flow_balance_difference
#print axioms OddCycle.carry_eq_unlimited
#print axioms OddCycle.targetOccurrences_complete
#print axioms OddCycle.unlimited_target_balance
#print axioms OddCycle.uniform_two_flow_identity
#print axioms OddCycle.uniform_defect
#print axioms OddCycle.uniform_defect_pos
#print axioms OddCycle.uniform_defect_neg
#print axioms OddCycle.uniform_defect_two
#print axioms OddCycle.uniform_scaled_not_stationary
#print axioms OddCycle.normalizedCanonicalWeight_pos
#print axioms OddCycle.normalizedCanonicalWeight_sum
#print axioms OddCycle.normalizedCanonicalWeight_not_stationary
#print axioms OddCycle.FiniteMarkov.returnBy_tendsto_one
#print axioms OddCycle.FiniteMarkov.stationary_exists_unique
#print axioms OddCycle.FiniteMarkov.closed_recurrent_state_exists
#print axioms OddCycle.balanced_recurrent_state
#print axioms OddCycle.queueMarkov_irreducible
#print axioms OddCycle.queue_returnBy_tendsto_one
#print axioms OddCycle.queue_stationary_iff
#print axioms OddCycle.queue_stationary_exists_unique
#print axioms OddCycle.queue_stationary_positive
#print axioms OddCycle.queue_normalized_not_stationary
#print axioms OddCycle.partiteColor_proper
#print axioms OddCycle.partiteColor_surjective
