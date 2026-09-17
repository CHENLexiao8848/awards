import JSP000078.DeletionConnector
import JSP000078.SharedVertexPathSplice
import JSP000078.GyarfasLemmaOne
import JSP000078.EndpointConfigurationBridge

/-!
# Comparing odd cycles with at most one common vertex

A clean connector away from a shared vertex combines complementary arcs
into two odd cycles whose total length is the two original cycle lengths
plus twice the connector length. This extends the longest-cycle comparison
to a one-vertex intersection without assuming the desired bound.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Complementary arcs of two odd cycles meeting only at their common
base give two odd cycles whose total includes the connector twice. -/
theorem exists_two_odd_cycles_of_shared_base_connector {x u v : V}
    {C D : G.Walk x x} (hC : C.IsCycle) (hCO : Odd C.length)
    (hD : D.IsCycle) (hDO : Odd D.length)
    (hDC : ∀ w ∈ D.support, w ∈ C.support → w = x)
    (huC : u ∈ C.support) (hvD : v ∈ D.support) (hux : u ≠ x) (hvx : v ≠ x)
    (q : G.Walk u v) (hq : q.IsPath)
    (hqC : ∀ w ∈ q.support, w ∈ C.support → w = u)
    (hqD : ∀ w ∈ q.support, w ∈ D.support → w = v) :
    ∃ E F : G.Walk x x, E.IsCycle ∧ F.IsCycle ∧ Odd E.length ∧ Odd F.length ∧
      E.length + F.length = C.length + D.length + 2 * q.length := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU₁C, hU₂C, _, hUC⟩ :=
    exists_cycle_arcs hC C.start_mem_support huC hux.symm
  obtain ⟨P₁, P₂, hP₁, hP₂, hP₁D, hP₂D, _, hPD⟩ :=
    exists_cycle_arcs hD D.start_mem_support hvD hvx.symm
  let splice (P : G.Walk x v) (U : G.Walk x u) : G.Walk x x :=
    (P.append q.reverse).append U.reverse
  have hsplice (P : G.Walk x v) (U : G.Walk x u) (hP : P.IsPath) (hU : U.IsPath)
      (hPS : ∀ w ∈ P.support, w ∈ D.support) (hUS : ∀ w ∈ U.support, w ∈ C.support) :
      (splice P U).IsCycle :=
    isCycle_shared_vertex_path_splice hP hq hU hPS hUS hDC hqC hqD hux hvx
  have hlen (P : G.Walk x v) (U : G.Walk x u) :
      (splice P U).length = P.length + U.length + q.length := by
    simp only [splice, Walk.length_append, Walk.length_reverse]
    omega
  have hPodd : Odd (P₁.length + P₂.length) := hPD.symm ▸ hDO
  have hUodd : Odd (U₁.length + U₂.length) := hUC.symm ▸ hCO
  rcases odd_complementary_length_pairing (t := q.length) hPodd hUodd with hpairs | hpairs
  · refine ⟨splice P₁ U₁, splice P₂ U₂, hsplice P₁ U₁ hP₁ hU₁ hP₁D hU₁C,
      hsplice P₂ U₂ hP₂ hU₂ hP₂D hU₂C, ?_, ?_, ?_⟩
    · simpa only [hlen] using hpairs.1
    · simpa only [hlen] using hpairs.2
    · rw [hlen, hlen]
      omega
  · refine ⟨splice P₁ U₂, splice P₂ U₁, hsplice P₁ U₂ hP₁ hU₂ hP₁D hU₂C,
      hsplice P₂ U₁ hP₂ hU₁ hP₂D hU₁C, ?_, ?_, ?_⟩
    · simpa only [hlen] using hpairs.1
    · simpa only [hlen] using hpairs.2
    · rw [hlen, hlen]
      omega

/-- An odd cycle meeting a longest odd cycle only at their common base
is strictly shorter in a vertex-2-connected graph. -/
theorem shared_base_odd_cycle_length_lt_longest [Fintype V]
    (hG : TwoVertexConnected G) {x : V} {C D : G.Walk x x}
    (hC : IsLongestOddCycle C) (hD : D.IsCycle) (hDO : Odd D.length)
    (hDC : ∀ w ∈ D.support, w ∈ C.support → w = x) : D.length < C.length := by
  obtain ⟨u, v, q, hq, huC, hux, hvD, hvx, huv, _, hqC, hqD⟩ :=
    exists_clean_connector_between_cycles_sharing_vertex hG hC.1 hD
      (fun w hwC hwD ↦ hDC w hwD hwC)
  obtain ⟨E, F, hE, hF, hEO, hFO, hsum⟩ :=
    exists_two_odd_cycles_of_shared_base_connector hC.1 hC.2.1 hD hDO hDC
      huC hvD hux hvx q hq hqC hqD
  have hEL := hC.2.2 x E hE hEO
  have hFL := hC.2.2 x F hF hFO
  have hqpos : 0 < q.length := Nat.pos_of_ne_zero fun h ↦ huv (Walk.eq_of_length_eq_zero h)
  omega

/-- The longest-odd-cycle comparison remains strict if the other odd
cycle has at most one common vertex, whether or not that vertex occurs. -/
theorem odd_cycle_length_lt_longest_of_intersection_subset_singleton [Fintype V]
    (hG : TwoVertexConnected G) {c d x : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : IsLongestOddCycle C) (hD : D.IsCycle) (hDO : Odd D.length)
    (hDC : ∀ w ∈ D.support, w ∈ C.support → w = x) : D.length < C.length := by
  classical
  by_cases hshared : ∃ w, w ∈ D.support ∧ w ∈ C.support
  · obtain ⟨w, hwD, hwC⟩ := hshared
    have hwx := hDC w hwD hwC
    have hxD : x ∈ D.support := hwx ▸ hwD
    have hxC : x ∈ C.support := hwx ▸ hwC
    let Cx := C.rotate x hxC
    let Dx := D.rotate x hxD
    have hCx : IsLongestOddCycle Cx := hC.rotate hxC
    have hDx : Dx.IsCycle := hD.rotate hxD
    have hDxO : Odd Dx.length := by simpa only [Dx, Walk.length_rotate] using hDO
    have hinter : ∀ z ∈ Dx.support, z ∈ Cx.support → z = x := by
      intro z hzD hzC
      exact hDC z ((D.mem_support_rotate_iff x hxD).mp hzD)
        ((C.mem_support_rotate_iff x hxC).mp hzC)
    have hlt := shared_base_odd_cycle_length_lt_longest hG hCx hDx hDxO hinter
    simpa only [Cx, Dx, Walk.length_rotate] using hlt
  · have hdis : Disjoint {w | w ∈ C.support} {w | w ∈ D.support} := by
      apply Set.disjoint_left.mpr
      intro w hwC hwD
      exact hshared ⟨w, hwD, hwC⟩
    exact outside_odd_cycle_length_lt_longest hG hC hD hDO hdis

end JSP000078
