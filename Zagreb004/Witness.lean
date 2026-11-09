import Zagreb004.Definitions

/-!
UNCOMPILED CANDIDATE. The edge list is copied from the supplied certificate.
Each reachability proof follows an actual edge; no metadata is assumed.
All finite computations below use ordinary `decide`, not native evaluation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Zagreb004.Witness

/-- Canonical 67-edge list on precisely 46 vertices. -/
def edgeList : List (Fin 46 × Fin 46) :=
  [(0, 7),
   (0, 8),
   (0, 9),
   (0, 10),
   (0, 24),
   (1, 11),
   (1, 12),
   (1, 13),
   (1, 14),
   (1, 15),
   (2, 11),
   (2, 16),
   (2, 17),
   (2, 18),
   (2, 19),
   (3, 7),
   (3, 12),
   (3, 16),
   (3, 20),
   (3, 21),
   (4, 8),
   (4, 13),
   (4, 17),
   (4, 22),
   (4, 23),
   (5, 9),
   (5, 14),
   (5, 18),
   (5, 20),
   (5, 22),
   (6, 10),
   (6, 15),
   (6, 19),
   (6, 21),
   (6, 23),
   (24, 45),
   (25, 34),
   (25, 35),
   (25, 45),
   (26, 27),
   (26, 36),
   (26, 45),
   (27, 28),
   (27, 37),
   (28, 29),
   (28, 38),
   (29, 30),
   (29, 39),
   (30, 31),
   (30, 40),
   (31, 32),
   (31, 41),
   (32, 33),
   (32, 42),
   (33, 34),
   (33, 43),
   (34, 44),
   (35, 36),
   (35, 44),
   (36, 37),
   (37, 38),
   (38, 39),
   (39, 40),
   (40, 41),
   (41, 42),
   (42, 43),
   (43, 44)]

def graph : SimpleGraph (Fin 46) where
  Adj u v := u ≠ v ∧ ((u, v) ∈ edgeList ∨ (v, u) ∈ edgeList)
  symm := by
    intro u v h
    exact ⟨Ne.symm h.1, h.2.symm⟩
  loopless := by
    intro u h
    exact h.1 rfl

instance : DecidableRel graph.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ ((u, v) ∈ edgeList ∨ (v, u) ∈ edgeList))
  infer_instance

private theorem reach_0 : graph.Reachable (0 : Fin 46) 0 :=
  SimpleGraph.Reachable.refl 0
private theorem reach_7 : graph.Reachable (0 : Fin 46) 7 := by
  have hedge : graph.Adj (0 : Fin 46) 7 := by decide +kernel
  exact reach_0.trans hedge.reachable
private theorem reach_8 : graph.Reachable (0 : Fin 46) 8 := by
  have hedge : graph.Adj (0 : Fin 46) 8 := by decide +kernel
  exact reach_0.trans hedge.reachable
private theorem reach_9 : graph.Reachable (0 : Fin 46) 9 := by
  have hedge : graph.Adj (0 : Fin 46) 9 := by decide +kernel
  exact reach_0.trans hedge.reachable
private theorem reach_10 : graph.Reachable (0 : Fin 46) 10 := by
  have hedge : graph.Adj (0 : Fin 46) 10 := by decide +kernel
  exact reach_0.trans hedge.reachable
private theorem reach_24 : graph.Reachable (0 : Fin 46) 24 := by
  have hedge : graph.Adj (0 : Fin 46) 24 := by decide +kernel
  exact reach_0.trans hedge.reachable
private theorem reach_3 : graph.Reachable (0 : Fin 46) 3 := by
  have hedge : graph.Adj (7 : Fin 46) 3 := by decide +kernel
  exact reach_7.trans hedge.reachable
private theorem reach_4 : graph.Reachable (0 : Fin 46) 4 := by
  have hedge : graph.Adj (8 : Fin 46) 4 := by decide +kernel
  exact reach_8.trans hedge.reachable
private theorem reach_5 : graph.Reachable (0 : Fin 46) 5 := by
  have hedge : graph.Adj (9 : Fin 46) 5 := by decide +kernel
  exact reach_9.trans hedge.reachable
private theorem reach_6 : graph.Reachable (0 : Fin 46) 6 := by
  have hedge : graph.Adj (10 : Fin 46) 6 := by decide +kernel
  exact reach_10.trans hedge.reachable
private theorem reach_45 : graph.Reachable (0 : Fin 46) 45 := by
  have hedge : graph.Adj (24 : Fin 46) 45 := by decide +kernel
  exact reach_24.trans hedge.reachable
private theorem reach_12 : graph.Reachable (0 : Fin 46) 12 := by
  have hedge : graph.Adj (3 : Fin 46) 12 := by decide +kernel
  exact reach_3.trans hedge.reachable
private theorem reach_16 : graph.Reachable (0 : Fin 46) 16 := by
  have hedge : graph.Adj (3 : Fin 46) 16 := by decide +kernel
  exact reach_3.trans hedge.reachable
private theorem reach_20 : graph.Reachable (0 : Fin 46) 20 := by
  have hedge : graph.Adj (3 : Fin 46) 20 := by decide +kernel
  exact reach_3.trans hedge.reachable
private theorem reach_21 : graph.Reachable (0 : Fin 46) 21 := by
  have hedge : graph.Adj (3 : Fin 46) 21 := by decide +kernel
  exact reach_3.trans hedge.reachable
private theorem reach_13 : graph.Reachable (0 : Fin 46) 13 := by
  have hedge : graph.Adj (4 : Fin 46) 13 := by decide +kernel
  exact reach_4.trans hedge.reachable
private theorem reach_17 : graph.Reachable (0 : Fin 46) 17 := by
  have hedge : graph.Adj (4 : Fin 46) 17 := by decide +kernel
  exact reach_4.trans hedge.reachable
private theorem reach_22 : graph.Reachable (0 : Fin 46) 22 := by
  have hedge : graph.Adj (4 : Fin 46) 22 := by decide +kernel
  exact reach_4.trans hedge.reachable
private theorem reach_23 : graph.Reachable (0 : Fin 46) 23 := by
  have hedge : graph.Adj (4 : Fin 46) 23 := by decide +kernel
  exact reach_4.trans hedge.reachable
private theorem reach_14 : graph.Reachable (0 : Fin 46) 14 := by
  have hedge : graph.Adj (5 : Fin 46) 14 := by decide +kernel
  exact reach_5.trans hedge.reachable
private theorem reach_18 : graph.Reachable (0 : Fin 46) 18 := by
  have hedge : graph.Adj (5 : Fin 46) 18 := by decide +kernel
  exact reach_5.trans hedge.reachable
private theorem reach_15 : graph.Reachable (0 : Fin 46) 15 := by
  have hedge : graph.Adj (6 : Fin 46) 15 := by decide +kernel
  exact reach_6.trans hedge.reachable
private theorem reach_19 : graph.Reachable (0 : Fin 46) 19 := by
  have hedge : graph.Adj (6 : Fin 46) 19 := by decide +kernel
  exact reach_6.trans hedge.reachable
private theorem reach_25 : graph.Reachable (0 : Fin 46) 25 := by
  have hedge : graph.Adj (45 : Fin 46) 25 := by decide +kernel
  exact reach_45.trans hedge.reachable
private theorem reach_26 : graph.Reachable (0 : Fin 46) 26 := by
  have hedge : graph.Adj (45 : Fin 46) 26 := by decide +kernel
  exact reach_45.trans hedge.reachable
private theorem reach_1 : graph.Reachable (0 : Fin 46) 1 := by
  have hedge : graph.Adj (12 : Fin 46) 1 := by decide +kernel
  exact reach_12.trans hedge.reachable
private theorem reach_2 : graph.Reachable (0 : Fin 46) 2 := by
  have hedge : graph.Adj (16 : Fin 46) 2 := by decide +kernel
  exact reach_16.trans hedge.reachable
private theorem reach_34 : graph.Reachable (0 : Fin 46) 34 := by
  have hedge : graph.Adj (25 : Fin 46) 34 := by decide +kernel
  exact reach_25.trans hedge.reachable
private theorem reach_35 : graph.Reachable (0 : Fin 46) 35 := by
  have hedge : graph.Adj (25 : Fin 46) 35 := by decide +kernel
  exact reach_25.trans hedge.reachable
private theorem reach_27 : graph.Reachable (0 : Fin 46) 27 := by
  have hedge : graph.Adj (26 : Fin 46) 27 := by decide +kernel
  exact reach_26.trans hedge.reachable
private theorem reach_36 : graph.Reachable (0 : Fin 46) 36 := by
  have hedge : graph.Adj (26 : Fin 46) 36 := by decide +kernel
  exact reach_26.trans hedge.reachable
private theorem reach_11 : graph.Reachable (0 : Fin 46) 11 := by
  have hedge : graph.Adj (1 : Fin 46) 11 := by decide +kernel
  exact reach_1.trans hedge.reachable
private theorem reach_33 : graph.Reachable (0 : Fin 46) 33 := by
  have hedge : graph.Adj (34 : Fin 46) 33 := by decide +kernel
  exact reach_34.trans hedge.reachable
private theorem reach_44 : graph.Reachable (0 : Fin 46) 44 := by
  have hedge : graph.Adj (34 : Fin 46) 44 := by decide +kernel
  exact reach_34.trans hedge.reachable
private theorem reach_28 : graph.Reachable (0 : Fin 46) 28 := by
  have hedge : graph.Adj (27 : Fin 46) 28 := by decide +kernel
  exact reach_27.trans hedge.reachable
private theorem reach_37 : graph.Reachable (0 : Fin 46) 37 := by
  have hedge : graph.Adj (27 : Fin 46) 37 := by decide +kernel
  exact reach_27.trans hedge.reachable
private theorem reach_32 : graph.Reachable (0 : Fin 46) 32 := by
  have hedge : graph.Adj (33 : Fin 46) 32 := by decide +kernel
  exact reach_33.trans hedge.reachable
private theorem reach_43 : graph.Reachable (0 : Fin 46) 43 := by
  have hedge : graph.Adj (33 : Fin 46) 43 := by decide +kernel
  exact reach_33.trans hedge.reachable
private theorem reach_29 : graph.Reachable (0 : Fin 46) 29 := by
  have hedge : graph.Adj (28 : Fin 46) 29 := by decide +kernel
  exact reach_28.trans hedge.reachable
private theorem reach_38 : graph.Reachable (0 : Fin 46) 38 := by
  have hedge : graph.Adj (28 : Fin 46) 38 := by decide +kernel
  exact reach_28.trans hedge.reachable
private theorem reach_31 : graph.Reachable (0 : Fin 46) 31 := by
  have hedge : graph.Adj (32 : Fin 46) 31 := by decide +kernel
  exact reach_32.trans hedge.reachable
private theorem reach_42 : graph.Reachable (0 : Fin 46) 42 := by
  have hedge : graph.Adj (32 : Fin 46) 42 := by decide +kernel
  exact reach_32.trans hedge.reachable
private theorem reach_30 : graph.Reachable (0 : Fin 46) 30 := by
  have hedge : graph.Adj (29 : Fin 46) 30 := by decide +kernel
  exact reach_29.trans hedge.reachable
private theorem reach_39 : graph.Reachable (0 : Fin 46) 39 := by
  have hedge : graph.Adj (29 : Fin 46) 39 := by decide +kernel
  exact reach_29.trans hedge.reachable
private theorem reach_41 : graph.Reachable (0 : Fin 46) 41 := by
  have hedge : graph.Adj (31 : Fin 46) 41 := by decide +kernel
  exact reach_31.trans hedge.reachable
private theorem reach_40 : graph.Reachable (0 : Fin 46) 40 := by
  have hedge : graph.Adj (30 : Fin 46) 40 := by decide +kernel
  exact reach_30.trans hedge.reachable

theorem connected : graph.Connected := by
  have hroot : ∀ v : Fin 46, graph.Reachable (0 : Fin 46) v := by
    intro v
    fin_cases v
    · exact reach_0
    · exact reach_1
    · exact reach_2
    · exact reach_3
    · exact reach_4
    · exact reach_5
    · exact reach_6
    · exact reach_7
    · exact reach_8
    · exact reach_9
    · exact reach_10
    · exact reach_11
    · exact reach_12
    · exact reach_13
    · exact reach_14
    · exact reach_15
    · exact reach_16
    · exact reach_17
    · exact reach_18
    · exact reach_19
    · exact reach_20
    · exact reach_21
    · exact reach_22
    · exact reach_23
    · exact reach_24
    · exact reach_25
    · exact reach_26
    · exact reach_27
    · exact reach_28
    · exact reach_29
    · exact reach_30
    · exact reach_31
    · exact reach_32
    · exact reach_33
    · exact reach_34
    · exact reach_35
    · exact reach_36
    · exact reach_37
    · exact reach_38
    · exact reach_39
    · exact reach_40
    · exact reach_41
    · exact reach_42
    · exact reach_43
    · exact reach_44
    · exact reach_45
  exact ⟨fun u v => (hroot u).symm.trans (hroot v)⟩

theorem degree_table : ∀ v : Fin 46,
    degree graph v = if v.val < 7 then 5 else if v.val < 25 then 2 else 3 := by
  intro v
  fin_cases v <;> decide +kernel

theorem exact_extrema : degreeExtrema graph := by
  unfold degreeExtrema
  simp only [degree_table]
  decide +kernel

theorem exact_size : size graph = 67 := by decide +kernel

theorem exact_first : firstZagreb graph = 436 := by
  unfold firstZagreb
  simp only [degree_table]
  decide +kernel

theorem exact_second : secondZagreb graph = 635 := by
  unfold secondZagreb
  simp only [degree_table]
  decide +kernel

theorem exact_gap : gap graph = 2 := by
  unfold gap
  rw [exact_size, exact_first, exact_second]
  norm_num

theorem exact_edge_types :
    edgeTypeCount graph 2 5 = 35 ∧
    edgeTypeCount graph 3 3 = 31 ∧
    edgeTypeCount graph 2 3 = 1 := by
  unfold edgeTypeCount
  simp only [degree_table]
  decide +kernel

theorem strict_violation : violates graph := by
  unfold violates
  rw [exact_size, exact_first, exact_second]
  norm_num

/-- The intended 46-vertex existence theorem, with actual graph hypotheses. -/
theorem is_counterexample : counterexample graph :=
  ⟨connected, exact_extrema, strict_violation⟩

theorem existence :
    ∃ G : SimpleGraph (Fin 46),
      ∃ d : DecidableRel G.Adj, @counterexample 46 G d := by
  exact ⟨graph, inferInstance, is_counterexample⟩

end Zagreb004.Witness
