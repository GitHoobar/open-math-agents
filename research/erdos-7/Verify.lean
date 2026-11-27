import OddLift
import OddReduction
import MultiplicityLift
import SlopeObstruction
import SharpRepair
import PrimeReplacement
import DepthBound

/-! Connect the checked repair theorem to the open problem and audit the axioms of the main results. -/

namespace OddCoverAudit

/-- The constructed repair proves the reduction's second hypothesis verbatim. -/
theorem repairStep : OMA.R_Erdos7_erdos_7_R1.H2 := OddLift.repair

/-- Only the existence of the partial cover remains to settle this route. -/
theorem fromSeed : OMA.R_Erdos7_erdos_7_R1.H1 → type_of% @Erdos7.erdos_7 :=
  fun seed => OMA.R_Erdos7_erdos_7_R1.main seed repairStep

end OddCoverAudit

#print axioms OddCoverAudit.repairStep
#print axioms OddCoverAudit.fromSeed
#print axioms SlopeObstruction.necessary
#print axioms SharpRepair.exists_iff
#print axioms SharpRepair.covers_at_card
#print axioms PrimeReplacement.coversAt
#print axioms DepthBound.bounded_execution
#print axioms DepthBound.active_prefix_bound
#print axioms MultiplicityLift.replace_family
#print axioms MultiplicityLift.two_families_force_factor_five
