import Zagreb004.Cores

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Zagreb004
open Family

theorem even_order_counterexample (n : ℕ) (hn : 46 ≤ n) (hp : n % 2 = 0) :
    ∃ G : SimpleGraph (Fin n), ∃ d : DecidableRel G.Adj, @counterexample n G d := by
  classical
  let t := (n-32)/2
  let e : Fin n ≃ (Fin 25 ⊕ Option (Fin (t+3) × Fin 2)) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_option, Fintype.card_prod]
      dsimp [t]
      omega)
  let G := relabel (joined Core7.graph Core7.attachment t) e
  have hd : degreeExtrema G := assembled_extrema Core7.graph Core7.attachment t e
    Core7.bounds Core7.attachment_degree Core7.has_five
  have hc : G.Connected := relabel_connected _ e
    (joined_connected Core7.graph Core7.attachment t Core7.connected)
  have ht : ∀ u v, G.Adj u v → allowed (min (degree G u) (degree G v))
      (max (degree G u) (degree G v)) := by
    intro u v huv
    exact assembled_edge_types Core7.graph Core7.attachment t e
      Core7.attachment_degree Core7.edge_degrees huv
  have h2 : degreeCount G 2 = 18 := by
    rw [assembled_degree_count _ _ _ _ 2 (by decide)]
    exact Core7.count_two
  have h5 : degreeCount G 5 = 7 := by
    rw [assembled_degree_count _ _ _ _ 5 (by decide)]
    exact Core7.count_five
  have hgap : 0 < gap G := even_family_positive G hd.1 ht h2 h5 hn
  obtain ⟨hnpos,hmpos⟩ := extrema_positive G hd
  exact ⟨G, inferInstance, hc, hd, (violates_iff_gap_pos G hnpos hmpos).mpr hgap⟩

theorem odd_order_counterexample (n : ℕ) (hn : 47 ≤ n) (hp : n % 2 = 1) :
    ∃ G : SimpleGraph (Fin n), ∃ d : DecidableRel G.Adj, @counterexample n G d := by
  classical
  let t := (n-25)/2
  let e : Fin n ≃ (Fin 18 ⊕ Option (Fin (t+3) × Fin 2)) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_option, Fintype.card_prod]
      dsimp [t]
      omega)
  let G := relabel (joined Core5.graph Core5.attachment t) e
  have hd : degreeExtrema G := assembled_extrema Core5.graph Core5.attachment t e
    Core5.bounds Core5.attachment_degree Core5.has_five
  have hc : G.Connected := relabel_connected _ e
    (joined_connected Core5.graph Core5.attachment t Core5.connected)
  have ht : ∀ u v, G.Adj u v → allowed (min (degree G u) (degree G v))
      (max (degree G u) (degree G v)) := by
    intro u v huv
    exact assembled_edge_types Core5.graph Core5.attachment t e
      Core5.attachment_degree Core5.edge_degrees huv
  have h2 : degreeCount G 2 = 13 := by
    rw [assembled_degree_count _ _ _ _ 2 (by decide)]
    exact Core5.count_two
  have h5 : degreeCount G 5 = 5 := by
    rw [assembled_degree_count _ _ _ _ 5 (by decide)]
    exact Core5.count_five
  have hgap : 0 < gap G := odd_family_positive G hd.1 ht h2 h5 hn
  obtain ⟨hnpos,hmpos⟩ := extrema_positive G hd
  exact ⟨G, inferInstance, hc, hd, (violates_iff_gap_pos G hnpos hmpos).mpr hgap⟩

/-- Actual graph counterexamples exist at every integer order at least 46. -/
theorem all_orders : AllOrdersTarget := by
  intro n hn
  by_cases hp : n % 2 = 0
  · exact even_order_counterexample n hn hp
  · exact odd_order_counterexample n (by omega) (by omega)

/-- The original full graph-theoretic target, with no additional hypotheses. -/
theorem fullTarget : FullTarget :=
  ⟨exists46, minimality, all_orders, extremal_classification⟩

end Zagreb004
