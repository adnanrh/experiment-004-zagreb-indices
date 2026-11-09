import Zagreb004.Targets

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Zagreb004

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Count vertices of a specified degree. -/
def degreeCount (k : ℕ) : ℕ := (Finset.univ.filter (fun v => degree G v = k)).card

/-- Weighted incidence counting with each undirected edge counted once. -/
theorem weighted_incidence (f : Fin n → ℚ) :
    (∑ p ∈ edges G, (f p.1 + f p.2)) = ∑ v, (degree G v : ℚ) * f v := by
  have hswap :
      (∑ u : Fin n, ∑ v : Fin n, if u < v ∧ G.Adj u v then f v else 0) =
      ∑ u : Fin n, ∑ v : Fin n, if v < u ∧ G.Adj u v then f u else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    simp only [G.adj_comm]
  calc
    _ = (∑ u : Fin n, ∑ v : Fin n, if u < v ∧ G.Adj u v then f u else 0) +
        (∑ u : Fin n, ∑ v : Fin n, if u < v ∧ G.Adj u v then f v else 0) := by
      simp only [edges, Finset.product_eq_sprod, Finset.sum_filter, Finset.sum_product, ite_add, Finset.sum_add_distrib, add_zero]
    _ = ∑ u : Fin n, ∑ v : Fin n, if G.Adj u v then f u else 0 := by
      rw [hswap, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : G.Adj u v
      · have hne : u ≠ v := h.ne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · simp [h, hlt, not_lt_of_gt hlt]
        · simp [h, hgt, not_lt_of_gt hgt]
      · simp [h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp [← Finset.sum_filter, degree]

/-- A symmetric edge weight is determined by the ten degree-pair counts. -/
theorem edge_profile_sum
    (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5)
    (f : ℕ → ℕ → ℚ) (hf : ∀ i j, f i j = f j i) :
    (∑ p ∈ edges G, f (degree G p.1) (degree G p.2)) =
    (edgeTypeCount G 2 2 : ℚ) * f 2 2 +
    (edgeTypeCount G 2 3 : ℚ) * f 2 3 +
    (edgeTypeCount G 2 4 : ℚ) * f 2 4 +
    (edgeTypeCount G 2 5 : ℚ) * f 2 5 +
    (edgeTypeCount G 3 3 : ℚ) * f 3 3 +
    (edgeTypeCount G 3 4 : ℚ) * f 3 4 +
    (edgeTypeCount G 3 5 : ℚ) * f 3 5 +
    (edgeTypeCount G 4 4 : ℚ) * f 4 4 +
    (edgeTypeCount G 4 5 : ℚ) * f 4 5 +
    (edgeTypeCount G 5 5 : ℚ) * f 5 5 := by
  have hc (i j : ℕ) : (edgeTypeCount G i j : ℚ) * f i j =
      ∑ p ∈ edges G, if min (degree G p.1) (degree G p.2) = i ∧
        max (degree G p.1) (degree G p.2) = j then f i j else 0 := by
    simp [edgeTypeCount, ← Finset.sum_filter]
  simp_rw [hc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨h1, h1'⟩ := hd p.1
  obtain ⟨h2, h2'⟩ := hd p.2
  generalize ha : degree G p.1 = a at *
  generalize hb : degree G p.2 = b at *
  interval_cases a <;> interval_cases b <;> norm_num [hf]


theorem profile_size (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    Profiles.profileSize (graphProfile G) = size G := by
  have h := edge_profile_sum G hd (fun _ _ => 1) (by intros; rfl)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  unfold Profiles.profileSize graphProfile
  unfold size
  exact_mod_cast h.symm

theorem profile_second (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    Profiles.profileM2 (graphProfile G) = secondZagreb G := by
  have h := edge_profile_sum G hd (fun a b => a*b) (by intros; ring)
  norm_num at h
  unfold Profiles.profileM2 graphProfile secondZagreb
  exact_mod_cast (by nlinarith [h] :
    4*(edgeTypeCount G 2 2 : ℚ)+6*edgeTypeCount G 2 3+8*edgeTypeCount G 2 4+
    10*edgeTypeCount G 2 5+9*edgeTypeCount G 3 3+12*edgeTypeCount G 3 4+
    15*edgeTypeCount G 3 5+16*edgeTypeCount G 4 4+20*edgeTypeCount G 4 5+
    25*edgeTypeCount G 5 5 = ∑ p ∈ edges G, (degree G p.1 : ℚ)*(degree G p.2 : ℚ))

theorem profile_first (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    Profiles.profileM1 (graphProfile G) = firstZagreb G := by
  have h := edge_profile_sum G hd (fun a b => a+b) (by intros; ring)
  have hi := weighted_incidence G (fun v => (degree G v : ℚ))
  norm_num at h
  rw [hi] at h
  have hf : (∑ v, (degree G v : ℚ) * degree G v) = (firstZagreb G : ℚ) := by
    simp [firstZagreb, pow_two]
  rw [hf] at h
  have he : (Profiles.profileM1 (graphProfile G) : ℚ) = firstZagreb G := by
    unfold Profiles.profileM1 graphProfile
    push_cast
    linarith
  exact_mod_cast he

theorem profile_order (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    Profiles.order60 (graphProfile G) = 60*n := by
  have h := edge_profile_sum G hd (fun a b => 60/a+60/b) (by intros; ring)
  have hi := weighted_incidence G (fun v => 60/(degree G v : ℚ))
  norm_num at h
  rw [hi] at h
  have hc : (∑ v, (degree G v : ℚ) * (60 / degree G v)) = 60*n := by
    have hz (v : Fin n) : (degree G v : ℚ) ≠ 0 := by
      have := (hd v).1
      exact_mod_cast (by omega : degree G v ≠ 0)
    simp [mul_div_cancel₀ _ (hz _), mul_comm]
  rw [hc] at h
  have he : (Profiles.order60 (graphProfile G) : ℚ) = 60*n := by
    unfold Profiles.order60 graphProfile
    push_cast
    linarith
  exact_mod_cast he

theorem degree_incidence (k : ℕ) :
    (∑ p ∈ edges G, ((if degree G p.1 = k then 1 else 0 : ℚ) +
      (if degree G p.2 = k then 1 else 0 : ℚ))) = k * (degreeCount G k : ℚ) := by
  rw [weighted_incidence G (fun v => if degree G v = k then 1 else 0)]
  calc
    _ = ∑ v : Fin n, if degree G v = k then (k : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with h <;> simp [h]
    _ = _ := by simp [← Finset.sum_filter, degreeCount, mul_comm]

theorem incidence2 (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    let c := graphProfile G
    2*c.e22+c.e23+c.e24+c.e25 = 2*degreeCount G 2 := by
  have h := edge_profile_sum G hd
    (fun a b => (if a = 2 then 1 else 0 : ℚ) + (if b = 2 then 1 else 0 : ℚ))
    (by intros; ring)
  rw [degree_incidence] at h
  norm_num at h
  norm_cast at h
  simpa [graphProfile, mul_comm] using h.symm

theorem incidence3 (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    let c := graphProfile G
    c.e23+2*c.e33+c.e34+c.e35 = 3*degreeCount G 3 := by
  have h := edge_profile_sum G hd
    (fun a b => (if a = 3 then 1 else 0 : ℚ) + (if b = 3 then 1 else 0 : ℚ))
    (by intros; ring)
  rw [degree_incidence] at h
  norm_num at h
  norm_cast at h
  simpa [graphProfile, mul_comm] using h.symm

theorem incidence4 (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    let c := graphProfile G
    c.e24+c.e34+2*c.e44+c.e45 = 4*degreeCount G 4 := by
  have h := edge_profile_sum G hd
    (fun a b => (if a = 4 then 1 else 0 : ℚ) + (if b = 4 then 1 else 0 : ℚ))
    (by intros; ring)
  rw [degree_incidence] at h
  norm_num at h
  norm_cast at h
  simpa [graphProfile, mul_comm] using h.symm

theorem incidence5 (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    let c := graphProfile G
    c.e25+c.e35+c.e45+2*c.e55 = 5*degreeCount G 5 := by
  have h := edge_profile_sum G hd
    (fun a b => (if a = 5 then 1 else 0 : ℚ) + (if b = 5 then 1 else 0 : ℚ))
    (by intros; ring)
  rw [degree_incidence] at h
  norm_num at h
  norm_cast at h
  simpa [graphProfile, mul_comm] using h.symm


/-- Universal quadratic identity for the actual graph, not an assumed profile. -/
theorem graph_gap_identity (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    (gap G : ℚ) =
      (2 * ((graphProfile G).e25 : ℚ) * (graphProfile G).e33 -
        (Profiles.penaltyA60 (graphProfile G) : ℚ) * (graphProfile G).e25 -
        (Profiles.penaltyB60 (graphProfile G) : ℚ) * (graphProfile G).e33 -
        (Profiles.penaltyC60 (graphProfile G) : ℚ)) / 60 := by
  have h := Profiles.gap_identity (graphProfile G)
  rw [profile_size G hd, profile_first G hd, profile_second G hd,
    profile_order G hd] at h
  push_cast at h
  simpa [gap] using h

theorem positive_gap_profile (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5)
    (hp : 0 < gap G) : Profiles.positiveGap (graphProfile G) := by
  have h := graph_gap_identity G hd
  have hp' : (0 : ℚ) < gap G := by exact_mod_cast hp
  unfold Profiles.positiveGap
  have he :
      (Profiles.penaltyA60 (graphProfile G) : ℚ) * (graphProfile G).e25 +
      (Profiles.penaltyB60 (graphProfile G) : ℚ) * (graphProfile G).e33 +
      (Profiles.penaltyC60 (graphProfile G) : ℚ) <
      2 * ((graphProfile G).e25 : ℚ) * (graphProfile G).e33 := by linarith
  exact_mod_cast he

theorem edge_type_exists {i j : ℕ} (h : 0 < edgeTypeCount G i j) :
    ∃ u v, G.Adj u v ∧ min (degree G u) (degree G v) = i ∧
      max (degree G u) (degree G v) = j := by
  obtain ⟨⟨u,v⟩, hp⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter] at hp
  have he := hp.1
  simp only [edges, Finset.mem_filter] at he
  exact ⟨u,v,he.2.2,hp.2⟩

theorem adj_type_positive {u v : Fin n} (ha : G.Adj u v) :
    0 < edgeTypeCount G (min (degree G u) (degree G v))
      (max (degree G u) (degree G v)) := by
  unfold edgeTypeCount
  apply Finset.card_pos.mpr
  rcases lt_or_gt_of_ne ha.ne with h | h
  · refine ⟨(u,v), ?_⟩
    simp [edges, h, ha]
  · refine ⟨(v,u), ?_⟩
    simp [edges, h, ha.symm, min_comm, max_comm]

omit [DecidableRel G.Adj] in
/-- A nontrivial vertex cut of a connected graph contains an edge. -/
theorem connected_crossing (hc : G.Connected) (P : Fin n → Prop)
    {u v : Fin n} (hu : P u) (hv : ¬ P v) :
    ∃ a b, G.Adj a b ∧ P a ∧ ¬ P b := by
  classical
  by_contra h
  have hclosed : ∀ a b, G.Adj a b → P a → P b := by
    intro a b hab hpa
    by_contra hpb
    exact h ⟨a,b,hab,hpa,hpb⟩
  obtain ⟨w⟩ := hc u v
  have hw : P u → P v := by
    clear hu hv
    induction w with
    | nil => exact id
    | @cons a b c hab w ih => exact fun ha => ih (hclosed a b hab ha)
  exact hv (hw hu)

/-- Both profile cut conditions follow from graph connectedness. -/
theorem profile_cuts (hc : G.Connected)
    (hd : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) :
    Profiles.cutConditions (graphProfile G) := by
  have vertices (ha : 0 < (graphProfile G).e25) (hb : 0 < (graphProfile G).e33) :
      ∃ u v, degree G u = 2 ∧ degree G v = 3 := by
    obtain ⟨a,b,_,hmin,hmax⟩ := edge_type_exists G ha
    obtain ⟨c,d,_,hcmin,hcmax⟩ := edge_type_exists G hb
    have hc3 : degree G c = 3 := by omega
    by_cases hab : degree G a ≤ degree G b
    · exact ⟨a,c,by simpa [min_eq_left hab] using hmin,hc3⟩
    · exact ⟨b,c,by simpa [min_eq_right (by omega : degree G b ≤ degree G a)] using hmin,hc3⟩
  constructor
  · intro ha hb
    obtain ⟨u,v,hu,hv⟩ := vertices ha hb
    obtain ⟨a,b,hab,ha3,hb3⟩ := connected_crossing G hc (fun x => degree G x = 3)
      hv (by omega : degree G u ≠ 3)
    have ht := adj_type_positive G hab
    obtain ⟨hlo,hhi⟩ := hd b
    change 0 < edgeTypeCount G 2 3 + edgeTypeCount G 3 4 + edgeTypeCount G 3 5
    rw [ha3] at ht
    generalize he : degree G b = k at *
    interval_cases k <;> norm_num at ht <;> omega
  · intro ha hb
    obtain ⟨u,v,hu,hv⟩ := vertices ha hb
    obtain ⟨a,b,hab,hpa,hpb⟩ := connected_crossing G hc
      (fun x => degree G x = 2 ∨ degree G x = 5) (u := u) (v := v)
      (Or.inl hu) (by simp [hv])
    have ht := adj_type_positive G hab
    obtain ⟨hal,hah⟩ := hd a
    obtain ⟨hbl,hbh⟩ := hd b
    change 0 < edgeTypeCount G 2 3 + edgeTypeCount G 2 4 +
      edgeTypeCount G 3 5 + edgeTypeCount G 4 5
    generalize he : degree G a = k at *
    generalize hf : degree G b = l at *
    interval_cases k <;> interval_cases l <;> norm_num at ht <;> omega

end Zagreb004
