import Zagreb004.GraphCounting
import Zagreb004.Witness

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Zagreb004
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem extrema_positive (hd : degreeExtrema G) : 0 < n ∧ 0 < size G := by
  obtain ⟨v,hv⟩ := hd.2.1
  have hn : 0 < n := by have := v.isLt; omega
  have hdeg : 0 < degree G v := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hdeg
  have ha : G.Adj v w := (Finset.mem_filter.mp hw).2
  have ht := adj_type_positive G ha
  have hs : edgeTypeCount G (min (degree G v) (degree G w))
      (max (degree G v) (degree G w)) ≤ size G :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact ⟨hn, by omega⟩

theorem violates_iff_gap_pos (hn : 0 < n) (hm : 0 < size G) :
    violates G ↔ 0 < gap G := by
  unfold violates
  rw [div_lt_div_iff₀ (by exact_mod_cast hm) (by exact_mod_cast hn)]
  constructor
  · intro h
    have hi : (secondZagreb G : ℤ)*n < (firstZagreb G : ℤ)*size G := by exact_mod_cast h
    unfold gap
    nlinarith
  · intro h
    have hi : (secondZagreb G : ℤ)*n < (firstZagreb G : ℤ)*size G := by
      unfold gap at h
      nlinarith
    exact_mod_cast hi

theorem small_counterexample_profile (hn : n ≤ 46) (hg : counterexample G) :
    graphProfile G = Profiles.canonical := by
  obtain ⟨hc,hd,hv⟩ := hg
  obtain ⟨hnpos,hmpos⟩ := extrema_positive G hd
  apply Profiles.profile_threshold (graphProfile G)
    (degreeCount G 2) (degreeCount G 3) (degreeCount G 4) (degreeCount G 5)
  · exact incidence2 G hd.1
  · exact incidence3 G hd.1
  · exact incidence4 G hd.1
  · exact incidence5 G hd.1
  · rw [profile_order G hd.1]
    omega
  · exact profile_cuts G hc hd.1
  · exact positive_gap_profile G hd.1 ((violates_iff_gap_pos G hnpos hmpos).mp hv)

/-- No qualifying graph of order at most 45 violates the Zagreb inequality. -/
theorem minimality : MinimalityTarget := by
  intro n G d hn hc hd
  by_contra h
  have hv : @violates n G d := lt_of_not_ge h
  have hp := small_counterexample_profile G (by omega) ⟨hc,hd,hv⟩
  have ho := profile_order G hd.1
  rw [hp] at ho
  norm_num [Profiles.order60, Profiles.canonical] at ho
  omega

/-- Every qualifying 46-vertex counterexample has the exact canonical profile. -/
theorem extremal_classification : ExtremalProfileTarget := by
  intro G d hg
  exact small_counterexample_profile G (by omega) hg

theorem exists46 : Exists46Target := Witness.existence

end Zagreb004
