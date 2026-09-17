import JSP000078.HubRigidity
import JSP000078.GyarfasLemmaSeven
import JSP000078.CycleCardinality

/-! # The distinct-attachment exception for parameters at least two -/

namespace JSP000078

open SimpleGraph

/-- Two outside endpoints each with 2k selected cycle neighbors cannot
coexist with only k odd lengths when k≥2. Overlap uses a shared attachment;
disjointness contradicts the order forced by the outside-hub rigidity. -/
theorem distinct_attachments_impossible_large
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (X Y : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hK : (oddCycleLengths G).card = k) (hXcard : X.card = 2 * k) (hYcard : Y.card = 2 * k)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ G.Adj A v)
    (hY : ∀ v ∈ Y, v ∈ C.support ∧ G.Adj B v) : False := by
  classical
  by_cases hdis : Disjoint X Y
  · have hA : A ∉ C.support := fun h ↦ Set.disjoint_left.mp hPC P.start_mem_support h
    have hN := odd_cycle_length_eq_of_outside_hub hC hCO hA X k hk hXcard hK hX
    have hsub : X ∪ Y ⊆ C.support.toFinset := by
      intro v hv
      rcases Finset.mem_union.mp hv with hx | hy
      · exact List.mem_toFinset.mpr (hX v hx).1
      · exact List.mem_toFinset.mpr (hY v hy).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, hXcard, hYcard, card_cycle_support hC, hN] at hcard
    omega
  · obtain ⟨x, hx, hy⟩ := Finset.not_disjoint_iff.mp hdis
    have hcount := odd_lengths_of_shared_attachment hC hCO hP hAB hPC X k
      (by omega) hXcard hX hx (hY x hy).2
    omega

end JSP000078
