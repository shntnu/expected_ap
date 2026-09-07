import ap_moments

-- Run from lean/: lake env lean verify.lean
-- Report exact types and transitive axiom dependencies of the paper's results.
#check ExpectedAp.expected_ap_closed_form
#print axioms ExpectedAp.expected_ap_closed_form
#check ExpectedAp.secondMomentAP_eq_expectedWSq_div
#print axioms ExpectedAp.secondMomentAP_eq_expectedWSq_div
#check ExpectedAp.varianceAP_closed_form
#print axioms ExpectedAp.varianceAP_closed_form
#check ExpectedAp.uniformAPMass_closed_form_explicit
#print axioms ExpectedAp.uniformAPMass_closed_form_explicit
#check ExpectedAp.sum_apPMF_eq_one
#print axioms ExpectedAp.sum_apPMF_eq_one
#check ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_zero
#print axioms ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_zero
#check ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_one
#print axioms ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_one
#check ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_card
#print axioms ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_card
