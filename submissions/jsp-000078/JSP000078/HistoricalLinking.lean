import JSP000078.InitialLinkage
import JSP000078.LinkageConnector
import JSP000078.LinkageReroute

/-!
# Two disjoint links between disjoint cycles

This is the vertex-connectivity fact used on pages 42-43 of Gyárfás's paper.
The proof minimizes the stem of a normalized two-arm configuration and
reroutes along a path avoiding its branch. No Menger theorem is assumed.
-/

namespace JSP000078

open SimpleGraph

/-- In a graph connected after every vertex deletion, disjoint simple cycles
have two vertex-disjoint links with interiors outside both cycles. -/
theorem twoDisjointCycleLinks_of_twoVertexConnected
    {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : TwoVertexConnected G) :
    TwoDisjointCycleLinks G := by
  classical
  intro c d C D hC hD hCD
  let A : Set V := {v | v ∈ C.support}
  let B : Set V := {v | v ∈ D.support}
  let candidate : ℕ → Prop := fun n ↦ ∃ Y : LinkageY G A B, Y.stem.length = n
  obtain ⟨Y₀⟩ := nonempty_linkageY_of_disjoint_cycles hG.2.1 C D hC hD hCD
  have hex : ∃ n, candidate n := ⟨Y₀.stem.length, Y₀, rfl⟩
  obtain ⟨Y, hlen⟩ := Nat.find_spec hex
  have hB : ∃ b ∈ B, b ≠ Y.branch := exists_mem_cycle_support_ne hD Y.branch
  obtain ⟨x, y, q, hx, hy, _, ht, hL, hR⟩ := Y.exists_connector hG hB
  let S := Y.sourcePair hx
  let W := S.front.append q
  obtain ⟨hWV, hWS, hWB⟩ := Y.connector_supports hCD S q ht hL hR
  by_cases hyS : y ∈ Y.stem.support
  · obtain ⟨Y', hshort⟩ := Y.exists_reroute_shorter S W hyS hy.2 hWV hWS hWB
    have hn : Y'.stem.length < Nat.find hex := by omega
    exact (Nat.find_min hex hn ⟨Y', rfl⟩).elim
  · have hyB : y ∈ B := hy.1.resolve_right hyS
    have hdis : Disjoint {v | v ∈ W.support}
        {v | v ∈ (S.arm.append Y.stem).support} := by
      apply Set.disjoint_left.mpr
      intro v hvW hvVS
      rcases (Walk.mem_support_append_iff S.arm Y.stem).mp hvVS with hvV | hvS
      · exact Set.disjoint_left.mp hWV hvW hvV
      · exact hyS (hWS v hvW hvS ▸ hvS)
    exact exists_trimmed_disjoint_links W (S.arm.append Y.stem)
      S.source_mem S.other_mem hyB Y.right_mem hdis

/-- The historical cycle-linking obligation is discharged without additional hypotheses. -/
theorem historicalCycleLinking : HistoricalCycleLinking := by
  intro V _ G hG
  exact twoDisjointCycleLinks_of_twoVertexConnected hG

end JSP000078
