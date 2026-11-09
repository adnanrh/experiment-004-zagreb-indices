import Zagreb004.GraphTheorems

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Zagreb004.Family

/-- The prism with the rung at zero subdivided by a new vertex. -/
def component (t : ℕ) : SimpleGraph (Option (Fin (t+3) × Fin 2)) where
  Adj
    | none, none => False
    | none, some y => y.1 = 0
    | some x, none => x.1 = 0
    | some x, some y =>
      (SimpleGraph.cycleGraph (t+3)).Adj x.1 y.1 ∧ x.2 = y.2 ∨
      x.1 = y.1 ∧ x.1 ≠ 0 ∧ x.2 ≠ y.2
  symm := by
    intro x y
    cases x <;> cases y <;> simp only
    · exact id
    · exact id
    · exact id
    · simp only [SimpleGraph.adj_comm, eq_comm, ne_eq]
      aesop
  loopless := by
    intro x
    cases x <;> simp

/-- Cycle walks remain available in either layer after the rung is subdivided. -/
def layer (t : ℕ) (b : Fin 2) :
    SimpleGraph.cycleGraph (t+3) →g component t where
  toFun i := some (i,b)
  map_rel' := by intro i j h; exact Or.inl ⟨h,rfl⟩

theorem component_connected (t : ℕ) : (component t).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (component t)).mpr
  refine ⟨none, ?_⟩
  intro v
  cases v with
  | none => exact SimpleGraph.Reachable.refl _
  | some v =>
    have h : (component t).Adj none (some (0,v.2)) := rfl
    exact h.reachable.trans (((SimpleGraph.cycleGraph_connected (n := t+2)) 0 v.1).map (layer t v.2))

noncomputable instance (t : ℕ) : DecidableRel (component t).Adj := Classical.decRel _

theorem component_neighbors_root (t : ℕ) :
    (component t).neighborFinset none = {some (0,0), some (0,1)} := by
  ext x
  cases x with
  | none => simp [component]
  | some x =>
    rcases x with ⟨i,b⟩
    fin_cases b <;> simp [component]

theorem component_degree_root (t : ℕ) : (component t).degree none = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, component_neighbors_root]
  apply Finset.card_pair
  intro h
  have hh := congrArg (fun x : Option (Fin (t+3) × Fin 2) => x.map Prod.snd) h
  norm_num at hh

theorem component_neighbors (t : ℕ) (i : Fin (t+3)) (b : Fin 2) :
    (component t).neighborFinset (some (i,b)) =
      {some (i-1,b), some (i+1,b), if i = 0 then none else some (i,b+1)} := by
  ext x
  cases x with
  | none => by_cases hi : i = 0 <;> simp [component, hi]
  | some x =>
    rcases x with ⟨j,c⟩
    have hc : (SimpleGraph.cycleGraph (t+3)).Adj i j ↔ j = i-1 ∨ j = i+1 := by
      have h := SimpleGraph.cycleGraph_neighborFinset (v := i)
      have := congrArg (fun s => j ∈ s) h
      simpa using this
    by_cases hi : i = 0
    · simp [SimpleGraph.mem_neighborFinset, component, hi, hc]
      aesop
    · fin_cases b <;> fin_cases c <;> simp [SimpleGraph.mem_neighborFinset, component, hi, hc] <;> aesop

theorem component_degree (t : ℕ) (v : Fin (t+3) × Fin 2) :
    (component t).degree (some v) = 3 := by
  rcases v with ⟨i,b⟩
  have hc : (Finset.card {i-1,i+1} : ℕ) = 2 := by
    rw [← SimpleGraph.cycleGraph_degree_two_le]
    exact SimpleGraph.cycleGraph_degree_three_le
  have hne : i-1 ≠ i+1 := by
    by_contra h
    simp [h] at hc
  have hb : b ≠ b+1 := by fin_cases b <;> decide
  rw [← SimpleGraph.card_neighborFinset_eq_degree, component_neighbors]
  split_ifs with hi
  · simp [hne]
  · simp [hne, hb]


section Bridge
variable {A B : Type} (H : SimpleGraph A) (K : SimpleGraph B) (a : A) (b : B)

/-- Disjoint graphs joined by exactly one bridge. -/
def bridge : SimpleGraph (A ⊕ B) where
  Adj
    | .inl x, .inl y => H.Adj x y
    | .inr x, .inr y => K.Adj x y
    | .inl x, .inr y => x = a ∧ y = b
    | .inr y, .inl x => x = a ∧ y = b
  symm := by
    intro x y
    cases x <;> cases y
    · exact fun h => h.symm
    · exact id
    · exact id
    · exact fun h => h.symm
  loopless := by intro x; cases x <;> simp

noncomputable instance : DecidableRel (bridge H K a b).Adj := Classical.decRel _

def bridgeLeft : H →g bridge H K a b where
  toFun := Sum.inl
  map_rel' := by intros; assumption

def bridgeRight : K →g bridge H K a b where
  toFun := Sum.inr
  map_rel' := by intros; assumption

theorem bridge_connected (hH : H.Connected) (hK : K.Connected) :
    (bridge H K a b).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl a, ?_⟩
  intro v
  cases v with
  | inl x => exact (hH a x).map (bridgeLeft H K a b)
  | inr y =>
    have h : (bridge H K a b).Adj (.inl a) (.inr b) := ⟨rfl,rfl⟩
    exact h.reachable.trans ((hK b y).map (bridgeRight H K a b))

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableRel H.Adj] [DecidableRel K.Adj]

omit [DecidableEq A] in
theorem degree_sum (x : A) : H.degree x = ∑ y, if H.Adj x y then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, H.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]

omit [DecidableRel K.Adj] in
theorem bridge_degree_left (x : A) :
    (bridge H K a b).degree (.inl x) = H.degree x + (if x = a then 1 else 0) := by
  classical
  rw [degree_sum, Fintype.sum_sum_type, degree_sum]
  by_cases hx : x = a <;> simp [bridge, hx, ← Finset.sum_filter]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

omit [DecidableRel H.Adj] in
theorem bridge_degree_right (y : B) :
    (bridge H K a b).degree (.inr y) = K.degree y + (if y = b then 1 else 0) := by
  classical
  rw [degree_sum, Fintype.sum_sum_type, degree_sum]
  by_cases hy : y = b <;> simp [bridge, hy, Nat.add_comm, ← Finset.sum_filter]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

end Bridge


section Relabel
variable {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
variable {n : ℕ} (e : Fin n ≃ V)

def relabel : SimpleGraph (Fin n) := H.comap e

instance : DecidableRel (relabel H e).Adj := fun _ _ => inferInstanceAs (Decidable (H.Adj _ _))

theorem relabel_degree (v : Fin n) : degree (relabel H e) v = H.degree (e v) := by
  rw [degree_eq_mathlib, degree_sum, degree_sum]
  exact e.sum_comp (fun w => if H.Adj (e v) w then 1 else 0)

omit [Fintype V] [DecidableRel H.Adj] in
theorem relabel_connected (h : H.Connected) : (relabel H e).Connected := by
  exact h.map (SimpleGraph.Iso.comap e H).symm.toHom e.symm.surjective

end Relabel

section Assembly
variable {A : Type} [Fintype A] [DecidableEq A]
variable (H : SimpleGraph A) [DecidableRel H.Adj] (a : A) (t : ℕ)

def joined := bridge H (component t) a none

noncomputable instance : DecidableRel (joined H a t).Adj := Classical.decRel _

def adjustedDegree (x : A) : ℕ := H.degree x + if x = a then 1 else 0

theorem joined_degree_left (x : A) :
    (joined H a t).degree (.inl x) = adjustedDegree H a x :=
  bridge_degree_left H (component t) a none x

omit [DecidableRel H.Adj] in
theorem joined_degree_right (y : Option (Fin (t+3) × Fin 2)) :
    (joined H a t).degree (.inr y) = 3 := by
  change (bridge H (component t) a none).degree (.inr y) = 3
  rw [bridge_degree_right]
  cases y with
  | none => simp [component_degree_root]
  | some v => simp [component_degree]

omit [Fintype A] [DecidableEq A] [DecidableRel H.Adj] in
theorem joined_connected (h : H.Connected) : (joined H a t).Connected :=
  bridge_connected H (component t) a none h (component_connected t)

variable {n : ℕ} (e : Fin n ≃ (A ⊕ Option (Fin (t+3) × Fin 2)))

theorem assembled_degree (v : Fin n) :
    degree (relabel (joined H a t) e) v =
      Sum.elim (adjustedDegree H a) (fun _ => 3) (e v) := by
  rw [relabel_degree]
  cases he : e v with
  | inl x => exact joined_degree_left H a t x
  | inr y => exact joined_degree_right H a t y

theorem assembled_degree_count (d : ℕ) (hd : d ≠ 3) :
    degreeCount (relabel (joined H a t) e) d =
      (Finset.univ.filter (fun x => adjustedDegree H a x = d)).card := by
  classical
  unfold degreeCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [assembled_degree]
  rw [show (∑ x, if Sum.elim (adjustedDegree H a) (fun _ => 3) (e x) = d then 1 else 0) =
    ∑ y, if Sum.elim (adjustedDegree H a) (fun _ => 3) y = d then 1 else 0 from
      e.sum_comp (fun y => if Sum.elim (adjustedDegree H a) (fun _ => 3) y = d then 1 else 0)]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Ne.symm hd, if_false, Finset.sum_const_zero, add_zero]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem assembled_bounds (hq : ∀ x, adjustedDegree H a x = 2 ∨ adjustedDegree H a x = 5) :
    ∀ v, 2 ≤ degree (relabel (joined H a t) e) v ∧ degree (relabel (joined H a t) e) v ≤ 5 := by
  intro v
  rw [assembled_degree]
  cases he : e v with
  | inl x => have := hq x; dsimp; omega
  | inr y => norm_num

theorem assembled_extrema
    (hq : ∀ x, adjustedDegree H a x = 2 ∨ adjustedDegree H a x = 5)
    (ha : adjustedDegree H a a = 2) (h5 : ∃ x, adjustedDegree H a x = 5) :
    degreeExtrema (relabel (joined H a t) e) := by
  refine ⟨assembled_bounds H a t e hq, ?_, ?_⟩
  · refine ⟨e.symm (.inl a), ?_⟩
    simp [assembled_degree, ha]
  · obtain ⟨x,hx⟩ := h5
    refine ⟨e.symm (.inl x), ?_⟩
    simp [assembled_degree, hx]

def allowed (i j : ℕ) : Prop :=
  (i = 2 ∧ j = 5) ∨ (i = 3 ∧ j = 3) ∨ (i = 2 ∧ j = 3)

theorem assembled_edge_types
    (ha : adjustedDegree H a a = 2)
    (hE : ∀ x y, H.Adj x y →
      min (adjustedDegree H a x) (adjustedDegree H a y) = 2 ∧
      max (adjustedDegree H a x) (adjustedDegree H a y) = 5)
    {u v : Fin n} (h : (relabel (joined H a t) e).Adj u v) :
    allowed (min (degree (relabel (joined H a t) e) u) (degree (relabel (joined H a t) e) v))
      (max (degree (relabel (joined H a t) e) u) (degree (relabel (joined H a t) e) v)) := by
  rw [assembled_degree, assembled_degree]
  change (joined H a t).Adj (e u) (e v) at h
  cases hu : e u with
  | inl x =>
    cases hv : e v with
    | inl y =>
      rw [hu,hv] at h
      exact Or.inl (hE x y h)
    | inr y =>
      rw [hu,hv] at h
      change x = a ∧ y = none at h
      simp [allowed, h.1, ha]
  | inr x =>
    cases hv : e v with
    | inl y =>
      rw [hu,hv] at h
      change y = a ∧ x = none at h
      simp [allowed, h.1, ha]
    | inr y => simp [allowed]

end Assembly


section FamilyGap
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
variable (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5)
variable (ht : ∀ u v, G.Adj u v →
  allowed (min (degree G u) (degree G v)) (max (degree G u) (degree G v)))

include ht in
theorem excluded_edge_type (i j : ℕ) (hij : ¬ allowed i j) : edgeTypeCount G i j = 0 := by
  by_contra h
  obtain ⟨u,v,huv,hmin,hmax⟩ := edge_type_exists G (by omega : 0 < edgeTypeCount G i j)
  have he := ht u v huv
  rw [hmin,hmax] at he
  exact hij he

include hd ht in
theorem even_family_positive
    (h2c : degreeCount G 2 = 18) (h5c : degreeCount G 5 = 7) (hn : 46 ≤ n) :
    0 < gap G := by
  let c := graphProfile G
  have h22 : c.e22 = 0 := excluded_edge_type G ht 2 2 (by simp [allowed])
  have h24 : c.e24 = 0 := excluded_edge_type G ht 2 4 (by simp [allowed])
  have h34 : c.e34 = 0 := excluded_edge_type G ht 3 4 (by simp [allowed])
  have h35 : c.e35 = 0 := excluded_edge_type G ht 3 5 (by simp [allowed])
  have h44 : c.e44 = 0 := excluded_edge_type G ht 4 4 (by simp [allowed])
  have h45 : c.e45 = 0 := excluded_edge_type G ht 4 5 (by simp [allowed])
  have h55 : c.e55 = 0 := excluded_edge_type G ht 5 5 (by simp [allowed])
  have hi2 := incidence2 G hd
  have hi5 := incidence5 G hd
  have ho := profile_order G hd
  have hg := graph_gap_identity G hd
  change 2*c.e22+c.e23+c.e24+c.e25 = 2*degreeCount G 2 at hi2
  change c.e25+c.e35+c.e45+2*c.e55 = 5*degreeCount G 5 at hi5
  rw [h2c] at hi2
  rw [h5c] at hi5
  have h25 : c.e25 = 35 := by omega
  have h23 : c.e23 = 1 := by omega
  change Profiles.order60 c = 60*n at ho
  change (gap G : ℚ) = (2*(c.e25 : ℚ)*c.e33 -
    (Profiles.penaltyA60 c : ℚ)*c.e25 - (Profiles.penaltyB60 c : ℚ)*c.e33 -
    (Profiles.penaltyC60 c : ℚ))/60 at hg
  simp [Profiles.order60, h22,h23,h24,h25,h34,h35,h44,h45,h55] at ho
  simp [Profiles.penaltyA60, Profiles.penaltyB60, Profiles.penaltyC60,
    h22,h23,h24,h25,h34,h35,h44,h45,h55] at hg
  have hoQ : (50 : ℚ)+42*35+40*(c.e33 : ℚ) = 60*n := by exact_mod_cast ho
  have hnQ : (46 : ℚ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℚ) < gap G := by linarith
  exact_mod_cast hpos

include hd ht in
theorem odd_family_positive
    (h2c : degreeCount G 2 = 13) (h5c : degreeCount G 5 = 5) (hn : 47 ≤ n) :
    0 < gap G := by
  let c := graphProfile G
  have h22 : c.e22 = 0 := excluded_edge_type G ht 2 2 (by simp [allowed])
  have h24 : c.e24 = 0 := excluded_edge_type G ht 2 4 (by simp [allowed])
  have h34 : c.e34 = 0 := excluded_edge_type G ht 3 4 (by simp [allowed])
  have h35 : c.e35 = 0 := excluded_edge_type G ht 3 5 (by simp [allowed])
  have h44 : c.e44 = 0 := excluded_edge_type G ht 4 4 (by simp [allowed])
  have h45 : c.e45 = 0 := excluded_edge_type G ht 4 5 (by simp [allowed])
  have h55 : c.e55 = 0 := excluded_edge_type G ht 5 5 (by simp [allowed])
  have hi2 := incidence2 G hd
  have hi5 := incidence5 G hd
  have ho := profile_order G hd
  have hg := graph_gap_identity G hd
  change 2*c.e22+c.e23+c.e24+c.e25 = 2*degreeCount G 2 at hi2
  change c.e25+c.e35+c.e45+2*c.e55 = 5*degreeCount G 5 at hi5
  rw [h2c] at hi2
  rw [h5c] at hi5
  have h25 : c.e25 = 25 := by omega
  have h23 : c.e23 = 1 := by omega
  change Profiles.order60 c = 60*n at ho
  change (gap G : ℚ) = (2*(c.e25 : ℚ)*c.e33 -
    (Profiles.penaltyA60 c : ℚ)*c.e25 - (Profiles.penaltyB60 c : ℚ)*c.e33 -
    (Profiles.penaltyC60 c : ℚ))/60 at hg
  simp [Profiles.order60, h22,h23,h24,h25,h34,h35,h44,h45,h55] at ho
  simp [Profiles.penaltyA60, Profiles.penaltyB60, Profiles.penaltyC60,
    h22,h23,h24,h25,h34,h35,h44,h45,h55] at hg
  have hoQ : (50 : ℚ)+42*25+40*(c.e33 : ℚ) = 60*n := by exact_mod_cast ho
  have hnQ : (47 : ℚ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℚ) < gap G := by linarith
  exact_mod_cast hpos

end FamilyGap

end Zagreb004.Family
