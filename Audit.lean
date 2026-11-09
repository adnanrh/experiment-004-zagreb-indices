import Zagreb004

/-!
Phase 2 audit of all public theorems, including the exact FullTarget proof.
Both theorem types and original target definitions are printed for comparison.
-/

#print axioms Zagreb004.degree_eq_mathlib
#print axioms Zagreb004.Arithmetic.coefficient_barrier
#print axioms Zagreb004.Arithmetic.patternII_impossible
#print axioms Zagreb004.Arithmetic.patternI_unique
#print axioms Zagreb004.Arithmetic.family_gap_identity
#print axioms Zagreb004.Arithmetic.even_order_identity
#print axioms Zagreb004.Arithmetic.odd_order_identity
#print axioms Zagreb004.Arithmetic.even_gap_identity
#print axioms Zagreb004.Arithmetic.odd_gap_identity
#print axioms Zagreb004.Arithmetic.even_gap_positive
#print axioms Zagreb004.Arithmetic.odd_gap_positive
#print axioms Zagreb004.Arithmetic.all_orders_parameters
#print axioms Zagreb004.Profiles.gap_identity
#print axioms Zagreb004.Profiles.profile_threshold
#print axioms Zagreb004.Witness.connected
#print axioms Zagreb004.Witness.degree_table
#print axioms Zagreb004.Witness.exact_extrema
#print axioms Zagreb004.Witness.exact_size
#print axioms Zagreb004.Witness.exact_first
#print axioms Zagreb004.Witness.exact_second
#print axioms Zagreb004.Witness.exact_gap
#print axioms Zagreb004.Witness.exact_edge_types
#print axioms Zagreb004.Witness.strict_violation
#print axioms Zagreb004.Witness.is_counterexample
#print axioms Zagreb004.Witness.existence

#check Zagreb004.Exists46Target
#check Zagreb004.MinimalityTarget
#check Zagreb004.AllOrdersTarget
#check Zagreb004.ExtremalProfileTarget
#check Zagreb004.FullTarget

#print axioms Zagreb004.weighted_incidence
#print axioms Zagreb004.edge_profile_sum
#print axioms Zagreb004.profile_size
#print axioms Zagreb004.profile_second
#print axioms Zagreb004.profile_first
#print axioms Zagreb004.profile_order
#print axioms Zagreb004.degree_incidence
#print axioms Zagreb004.incidence2
#print axioms Zagreb004.incidence3
#print axioms Zagreb004.incidence4
#print axioms Zagreb004.incidence5
#print axioms Zagreb004.graph_gap_identity
#print axioms Zagreb004.positive_gap_profile
#print axioms Zagreb004.edge_type_exists
#print axioms Zagreb004.adj_type_positive
#print axioms Zagreb004.connected_crossing
#print axioms Zagreb004.profile_cuts
#print axioms Zagreb004.extrema_positive
#print axioms Zagreb004.violates_iff_gap_pos
#print axioms Zagreb004.small_counterexample_profile
#print axioms Zagreb004.minimality
#print axioms Zagreb004.extremal_classification
#print axioms Zagreb004.exists46
#check (Zagreb004.minimality : Zagreb004.MinimalityTarget)
#check (Zagreb004.extremal_classification : Zagreb004.ExtremalProfileTarget)

#print axioms Zagreb004.Family.component_connected
#print axioms Zagreb004.Family.component_neighbors_root
#print axioms Zagreb004.Family.component_degree_root
#print axioms Zagreb004.Family.component_neighbors
#print axioms Zagreb004.Family.component_degree
#print axioms Zagreb004.Family.bridge_connected
#print axioms Zagreb004.Family.degree_sum
#print axioms Zagreb004.Family.bridge_degree_left
#print axioms Zagreb004.Family.bridge_degree_right
#print axioms Zagreb004.Family.relabel_degree
#print axioms Zagreb004.Family.relabel_connected
#print axioms Zagreb004.Family.joined_degree_left
#print axioms Zagreb004.Family.joined_degree_right
#print axioms Zagreb004.Family.joined_connected
#print axioms Zagreb004.Family.assembled_degree
#print axioms Zagreb004.Family.assembled_degree_count
#print axioms Zagreb004.Family.assembled_bounds
#print axioms Zagreb004.Family.assembled_extrema
#print axioms Zagreb004.Family.assembled_edge_types
#print axioms Zagreb004.Family.excluded_edge_type
#print axioms Zagreb004.Family.even_family_positive
#print axioms Zagreb004.Family.odd_family_positive
#print axioms Zagreb004.Family.Core5.connected
#print axioms Zagreb004.Family.Core5.adjusted_table
#print axioms Zagreb004.Family.Core5.bounds
#print axioms Zagreb004.Family.Core5.attachment_degree
#print axioms Zagreb004.Family.Core5.has_five
#print axioms Zagreb004.Family.Core5.edge_degrees
#print axioms Zagreb004.Family.Core5.count_two
#print axioms Zagreb004.Family.Core5.count_five
#print axioms Zagreb004.Family.Core7.connected
#print axioms Zagreb004.Family.Core7.adjusted_table
#print axioms Zagreb004.Family.Core7.bounds
#print axioms Zagreb004.Family.Core7.attachment_degree
#print axioms Zagreb004.Family.Core7.has_five
#print axioms Zagreb004.Family.Core7.edge_degrees
#print axioms Zagreb004.Family.Core7.count_two
#print axioms Zagreb004.Family.Core7.count_five
#print axioms Zagreb004.even_order_counterexample
#print axioms Zagreb004.odd_order_counterexample
#print axioms Zagreb004.all_orders
#print axioms Zagreb004.fullTarget

#check (Zagreb004.all_orders : Zagreb004.AllOrdersTarget)
#check (Zagreb004.fullTarget : Zagreb004.FullTarget)
#print Zagreb004.FullTarget
#print Zagreb004.MinimalityTarget
#print Zagreb004.ExtremalProfileTarget
#print Zagreb004.AllOrdersTarget
#print Zagreb004.counterexample
#print Zagreb004.degreeExtrema
#print Zagreb004.fullTarget
