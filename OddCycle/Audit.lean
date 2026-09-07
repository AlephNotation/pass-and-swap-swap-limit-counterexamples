import OddCycle.Conclusions
import OddCycle.GeneralClosure
import OddCycle.GeneralHeight
import OddCycle.GeneralCommunication

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
