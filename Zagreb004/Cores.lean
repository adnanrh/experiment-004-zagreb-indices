import Zagreb004.Family

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Zagreb004.Family

namespace Core5

def edgeList : List (Fin 18 × Fin 18) :=
  [(0, 5), (1, 5), (0, 6), (1, 6), (1, 7), (2, 7), (1, 8), (2, 8), (2, 9), (3, 9), (2, 10), (3, 10), (3, 11), (4, 11), (3, 12), (4, 12), (4, 13), (0, 13), (4, 14), (0, 14), (1, 15), (2, 15), (3, 16), (4, 16), (0, 17)
]

def graph : SimpleGraph (Fin 18) where
  Adj x y := x ≠ y ∧ ((x,y) ∈ edgeList ∨ (y,x) ∈ edgeList)
  symm := by intro x y h; exact ⟨Ne.symm h.1,h.2.symm⟩
  loopless := by intro x h; exact h.1 rfl

instance : DecidableRel graph.Adj := by
  intro x y
  change Decidable (x ≠ y ∧ ((x,y) ∈ edgeList ∨ (y,x) ∈ edgeList))
  infer_instance

def attachment : Fin 18 := 17

private theorem reach0 : graph.Reachable (0 : Fin 18) 0 := SimpleGraph.Reachable.refl _
private theorem reach5 : graph.Reachable (0 : Fin 18) 5 :=
  reach0.trans (show graph.Adj 0 5 by decide +kernel).reachable
private theorem reach6 : graph.Reachable (0 : Fin 18) 6 :=
  reach0.trans (show graph.Adj 0 6 by decide +kernel).reachable
private theorem reach13 : graph.Reachable (0 : Fin 18) 13 :=
  reach0.trans (show graph.Adj 0 13 by decide +kernel).reachable
private theorem reach14 : graph.Reachable (0 : Fin 18) 14 :=
  reach0.trans (show graph.Adj 0 14 by decide +kernel).reachable
private theorem reach17 : graph.Reachable (0 : Fin 18) 17 :=
  reach0.trans (show graph.Adj 0 17 by decide +kernel).reachable
private theorem reach1 : graph.Reachable (0 : Fin 18) 1 :=
  reach5.trans (show graph.Adj 5 1 by decide +kernel).reachable
private theorem reach4 : graph.Reachable (0 : Fin 18) 4 :=
  reach13.trans (show graph.Adj 13 4 by decide +kernel).reachable
private theorem reach7 : graph.Reachable (0 : Fin 18) 7 :=
  reach1.trans (show graph.Adj 1 7 by decide +kernel).reachable
private theorem reach8 : graph.Reachable (0 : Fin 18) 8 :=
  reach1.trans (show graph.Adj 1 8 by decide +kernel).reachable
private theorem reach15 : graph.Reachable (0 : Fin 18) 15 :=
  reach1.trans (show graph.Adj 1 15 by decide +kernel).reachable
private theorem reach11 : graph.Reachable (0 : Fin 18) 11 :=
  reach4.trans (show graph.Adj 4 11 by decide +kernel).reachable
private theorem reach12 : graph.Reachable (0 : Fin 18) 12 :=
  reach4.trans (show graph.Adj 4 12 by decide +kernel).reachable
private theorem reach16 : graph.Reachable (0 : Fin 18) 16 :=
  reach4.trans (show graph.Adj 4 16 by decide +kernel).reachable
private theorem reach2 : graph.Reachable (0 : Fin 18) 2 :=
  reach7.trans (show graph.Adj 7 2 by decide +kernel).reachable
private theorem reach3 : graph.Reachable (0 : Fin 18) 3 :=
  reach11.trans (show graph.Adj 11 3 by decide +kernel).reachable
private theorem reach9 : graph.Reachable (0 : Fin 18) 9 :=
  reach2.trans (show graph.Adj 2 9 by decide +kernel).reachable
private theorem reach10 : graph.Reachable (0 : Fin 18) 10 :=
  reach2.trans (show graph.Adj 2 10 by decide +kernel).reachable

theorem connected : graph.Connected := by
  have h : ∀ v : Fin 18, graph.Reachable 0 v := by
    intro v
    fin_cases v
    · exact reach0
    · exact reach1
    · exact reach2
    · exact reach3
    · exact reach4
    · exact reach5
    · exact reach6
    · exact reach7
    · exact reach8
    · exact reach9
    · exact reach10
    · exact reach11
    · exact reach12
    · exact reach13
    · exact reach14
    · exact reach15
    · exact reach16
    · exact reach17
  exact ⟨fun x y => (h x).symm.trans (h y)⟩

theorem adjusted_table (v : Fin 18) :
    adjustedDegree graph attachment v = if v.val < 5 then 5 else 2 := by
  unfold adjustedDegree
  rw [← degree_eq_mathlib]
  fin_cases v <;> decide +kernel

theorem bounds (v : Fin 18) :
    adjustedDegree graph attachment v = 2 ∨ adjustedDegree graph attachment v = 5 := by
  rw [adjusted_table]
  split_ifs <;> simp

theorem attachment_degree : adjustedDegree graph attachment attachment = 2 := by
  rw [adjusted_table]
  decide

theorem has_five : ∃ v, adjustedDegree graph attachment v = 5 := by
  exact ⟨0, by rw [adjusted_table]; decide⟩

theorem edge_degrees : ∀ x y, graph.Adj x y →
    min (adjustedDegree graph attachment x) (adjustedDegree graph attachment y) = 2 ∧
    max (adjustedDegree graph attachment x) (adjustedDegree graph attachment y) = 5 := by
  simp_rw [adjusted_table]
  decide +kernel

theorem count_two :
    (Finset.univ.filter (fun v => adjustedDegree graph attachment v = 2)).card = 13 := by
  simp_rw [adjusted_table]
  decide +kernel

theorem count_five :
    (Finset.univ.filter (fun v => adjustedDegree graph attachment v = 5)).card = 5 := by
  simp_rw [adjusted_table]
  decide +kernel

end Core5

namespace Core7

def edgeList : List (Fin 25 × Fin 25) :=
  [(0, 7), (1, 7), (0, 8), (1, 8), (1, 9), (2, 9), (1, 10), (2, 10), (2, 11), (3, 11), (2, 12), (3, 12), (3, 13), (4, 13), (3, 14), (4, 14), (4, 15), (5, 15), (4, 16), (5, 16), (5, 17), (6, 17), (5, 18), (6, 18), (6, 19), (0, 19), (6, 20), (0, 20), (1, 21), (2, 21), (3, 22), (4, 22), (5, 23), (6, 23), (0, 24)
]

def graph : SimpleGraph (Fin 25) where
  Adj x y := x ≠ y ∧ ((x,y) ∈ edgeList ∨ (y,x) ∈ edgeList)
  symm := by intro x y h; exact ⟨Ne.symm h.1,h.2.symm⟩
  loopless := by intro x h; exact h.1 rfl

instance : DecidableRel graph.Adj := by
  intro x y
  change Decidable (x ≠ y ∧ ((x,y) ∈ edgeList ∨ (y,x) ∈ edgeList))
  infer_instance

def attachment : Fin 25 := 24

private theorem reach0 : graph.Reachable (0 : Fin 25) 0 := SimpleGraph.Reachable.refl _
private theorem reach7 : graph.Reachable (0 : Fin 25) 7 :=
  reach0.trans (show graph.Adj 0 7 by decide +kernel).reachable
private theorem reach8 : graph.Reachable (0 : Fin 25) 8 :=
  reach0.trans (show graph.Adj 0 8 by decide +kernel).reachable
private theorem reach19 : graph.Reachable (0 : Fin 25) 19 :=
  reach0.trans (show graph.Adj 0 19 by decide +kernel).reachable
private theorem reach20 : graph.Reachable (0 : Fin 25) 20 :=
  reach0.trans (show graph.Adj 0 20 by decide +kernel).reachable
private theorem reach24 : graph.Reachable (0 : Fin 25) 24 :=
  reach0.trans (show graph.Adj 0 24 by decide +kernel).reachable
private theorem reach1 : graph.Reachable (0 : Fin 25) 1 :=
  reach7.trans (show graph.Adj 7 1 by decide +kernel).reachable
private theorem reach6 : graph.Reachable (0 : Fin 25) 6 :=
  reach19.trans (show graph.Adj 19 6 by decide +kernel).reachable
private theorem reach9 : graph.Reachable (0 : Fin 25) 9 :=
  reach1.trans (show graph.Adj 1 9 by decide +kernel).reachable
private theorem reach10 : graph.Reachable (0 : Fin 25) 10 :=
  reach1.trans (show graph.Adj 1 10 by decide +kernel).reachable
private theorem reach21 : graph.Reachable (0 : Fin 25) 21 :=
  reach1.trans (show graph.Adj 1 21 by decide +kernel).reachable
private theorem reach17 : graph.Reachable (0 : Fin 25) 17 :=
  reach6.trans (show graph.Adj 6 17 by decide +kernel).reachable
private theorem reach18 : graph.Reachable (0 : Fin 25) 18 :=
  reach6.trans (show graph.Adj 6 18 by decide +kernel).reachable
private theorem reach23 : graph.Reachable (0 : Fin 25) 23 :=
  reach6.trans (show graph.Adj 6 23 by decide +kernel).reachable
private theorem reach2 : graph.Reachable (0 : Fin 25) 2 :=
  reach9.trans (show graph.Adj 9 2 by decide +kernel).reachable
private theorem reach5 : graph.Reachable (0 : Fin 25) 5 :=
  reach17.trans (show graph.Adj 17 5 by decide +kernel).reachable
private theorem reach11 : graph.Reachable (0 : Fin 25) 11 :=
  reach2.trans (show graph.Adj 2 11 by decide +kernel).reachable
private theorem reach12 : graph.Reachable (0 : Fin 25) 12 :=
  reach2.trans (show graph.Adj 2 12 by decide +kernel).reachable
private theorem reach15 : graph.Reachable (0 : Fin 25) 15 :=
  reach5.trans (show graph.Adj 5 15 by decide +kernel).reachable
private theorem reach16 : graph.Reachable (0 : Fin 25) 16 :=
  reach5.trans (show graph.Adj 5 16 by decide +kernel).reachable
private theorem reach3 : graph.Reachable (0 : Fin 25) 3 :=
  reach11.trans (show graph.Adj 11 3 by decide +kernel).reachable
private theorem reach4 : graph.Reachable (0 : Fin 25) 4 :=
  reach15.trans (show graph.Adj 15 4 by decide +kernel).reachable
private theorem reach13 : graph.Reachable (0 : Fin 25) 13 :=
  reach3.trans (show graph.Adj 3 13 by decide +kernel).reachable
private theorem reach14 : graph.Reachable (0 : Fin 25) 14 :=
  reach3.trans (show graph.Adj 3 14 by decide +kernel).reachable
private theorem reach22 : graph.Reachable (0 : Fin 25) 22 :=
  reach3.trans (show graph.Adj 3 22 by decide +kernel).reachable

theorem connected : graph.Connected := by
  have h : ∀ v : Fin 25, graph.Reachable 0 v := by
    intro v
    fin_cases v
    · exact reach0
    · exact reach1
    · exact reach2
    · exact reach3
    · exact reach4
    · exact reach5
    · exact reach6
    · exact reach7
    · exact reach8
    · exact reach9
    · exact reach10
    · exact reach11
    · exact reach12
    · exact reach13
    · exact reach14
    · exact reach15
    · exact reach16
    · exact reach17
    · exact reach18
    · exact reach19
    · exact reach20
    · exact reach21
    · exact reach22
    · exact reach23
    · exact reach24
  exact ⟨fun x y => (h x).symm.trans (h y)⟩

theorem adjusted_table (v : Fin 25) :
    adjustedDegree graph attachment v = if v.val < 7 then 5 else 2 := by
  unfold adjustedDegree
  rw [← degree_eq_mathlib]
  fin_cases v <;> decide +kernel

theorem bounds (v : Fin 25) :
    adjustedDegree graph attachment v = 2 ∨ adjustedDegree graph attachment v = 5 := by
  rw [adjusted_table]
  split_ifs <;> simp

theorem attachment_degree : adjustedDegree graph attachment attachment = 2 := by
  rw [adjusted_table]
  decide

theorem has_five : ∃ v, adjustedDegree graph attachment v = 5 := by
  exact ⟨0, by rw [adjusted_table]; decide⟩

theorem edge_degrees : ∀ x y, graph.Adj x y →
    min (adjustedDegree graph attachment x) (adjustedDegree graph attachment y) = 2 ∧
    max (adjustedDegree graph attachment x) (adjustedDegree graph attachment y) = 5 := by
  simp_rw [adjusted_table]
  decide +kernel

theorem count_two :
    (Finset.univ.filter (fun v => adjustedDegree graph attachment v = 2)).card = 18 := by
  simp_rw [adjusted_table]
  decide +kernel

theorem count_five :
    (Finset.univ.filter (fun v => adjustedDegree graph attachment v = 5)).card = 7 := by
  simp_rw [adjusted_table]
  decide +kernel

end Core7

end Zagreb004.Family
