import ThirdOrderBounds
import ThirdOrderTail
import ThirdOrderDeletion
import ThirdOrderAvoidance
import ThirdOrderCRT
import ThirdOrderAllocation
import ThirdOrderProducts
import ThirdOrderUnlabel
import ThirdOrderMain

/-! Kernel axiom audit for the third-order CRT coverage manuscript. -/

#print axioms ThirdOrderBounds.coordinate_monotone
#print axioms ThirdOrderBounds.mass_le_five_B
#print axioms ThirdOrderTail.truncation_le_powerset_sum
#print axioms ThirdOrderDeletion.signedQ_positive_induced
#print axioms ThirdOrderAvoidance.finite_avoidance_ge
#print axioms ThirdOrderCRT.card_event
#print axioms ThirdOrderCRT.independent_avoidance
#print axioms ThirdOrderAllocation.all_tuple_mass
#print axioms ThirdOrderProducts.ordered_formula
#print axioms ThirdOrderProducts.cubic_identity
#print axioms ThirdOrderUnlabel.factorial_matching_mass
#print axioms ThirdOrderMain.odd_divisor_coverage
