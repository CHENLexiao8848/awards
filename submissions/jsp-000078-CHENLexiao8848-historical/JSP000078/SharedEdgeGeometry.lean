import JSP000078.CommonEdgeNoAdjacent
import JSP000078.CommonAttachmentGeometry
import JSP000078.ComplementaryParitySelection

/-!
# Length witnesses for the shared-endpoint-edge exception

An edge between the outside endpoints supplies a triangle and a three-edge
connector. Longestness excludes near-base attachments, so both original
and reflected selected distances are at least two.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Direct and complementary arc choices both supply the triangle and
the three connector-length memberships needed for the shared-edge count. -/
theorem shared_edge_attachment_memberships {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B} (hC : IsLongestOddCycle C)
    (hP : P.IsPath)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hAB : G.Adj A B) (hAc : G.Adj A c) (hBc : G.Adj B c)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 1 ≤ d ∧ d < C.length)
    (hAdj : ∀ d ∈ D, G.Adj A (C.getVert d)) {t : ℕ}
    (ht : t ∈ D ∨ ∃ d ∈ D, t = C.length - d) :
    (2 ≤ t ∧ t + 2 ≤ C.length) ∧ 3 ∈ oddCycleLengths G ∧
      (Odd (t + 2) → t + 2 ∈ oddCycleLengths G) ∧
      (Odd (t + 3) → t + 3 ∈ oddCycleLengths G) ∧
      (Odd (t + P.length + 2) → t + P.length + 2 ∈ oddCycleLengths G) := by
  have hA : A ∉ C.support := fun h ↦ Set.disjoint_left.mp hPC P.start_mem_support h
  have hB : B ∉ C.support := fun h ↦ Set.disjoint_left.mp hPC P.end_mem_support h
  have hEdgeC : Disjoint {v | v ∈ hAB.toWalk.support} {v | v ∈ C.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hvC
    have hvAB : v = A ∨ v = B := by simpa using hv
    rcases hvAB with rfl | rfl
    · exact hA hvC
    · exact hB hvC
  have hEdgeLen : hAB.toWalk.length = 1 := by simp
  have htriangle : 3 ∈ oddCycleLengths G := by
    obtain ⟨E, hE, hlen⟩ :=
      exists_cycle_of_common_attachment hAB.isPath_toWalk hAB.ne hEdgeC hAc hBc
    apply (mem_oddCycleLengths G).mpr
    exact ⟨by decide, A, E, hE, by simpa only [hEdgeLen] using hlen⟩
  have hlocal (d : ℕ) (hd : d ∈ D) :=
    common_attachment_cycle_memberships hC.1 hP hAB.ne hPC
      (hD d hd).1 (hD d hd).2 hAc hBc (hAdj d hd)
  have hedge (d : ℕ) (hd : d ∈ D) :=
    common_attachment_cycle_memberships hC.1 hAB.isPath_toWalk hAB.ne hEdgeC
      (hD d hd).1 (hD d hd).2 hAc hBc (hAdj d hd)
  have hbnds (d : ℕ) (hd : d ∈ D) :=
    common_edge_attachment_positions_not_near_base hC hA hB hAB
      (hD d hd).1 (hD d hd).2 (hAdj d hd) hBc
  rcases ht with ht | ⟨d, hd, rfl⟩
  · refine ⟨hbnds t ht, htriangle, (hlocal t ht).1, ?_, ?_⟩
    · simpa only [hEdgeLen, Nat.add_comm 1 t, Nat.add_assoc] using (hedge t ht).2.2.1
    · simpa only [Nat.add_comm P.length t] using (hlocal t ht).2.2.1
  · refine ⟨?_, htriangle, (hlocal d hd).2.1, ?_, ?_⟩
    · have h := hbnds d hd
      omega
    · simpa only [hEdgeLen, Nat.add_comm 1 (C.length - d), Nat.add_assoc] using
        (hedge d hd).2.2.2.1
    · simpa only [Nat.add_comm P.length (C.length - d)] using (hlocal d hd).2.2.2.1

/-- Every distance selected by complementary parity has the strict
interior bounds and all three odd-length memberships. The triangle
membership is supplied independently of whether the distance set is empty. -/
theorem shared_edge_complementary_distances_data {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B} (hC : IsLongestOddCycle C)
    (hP : P.IsPath)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hAB : G.Adj A B) (hAc : G.Adj A c) (hBc : G.Adj B c)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 1 ≤ d ∧ d < C.length)
    (hAdj : ∀ d ∈ D, G.Adj A (C.getVert d)) (r : ℕ) :
    3 ∈ oddCycleLengths G ∧
      ∀ t ∈ complementaryParityDistances D C.length r,
        (2 ≤ t ∧ t + 2 ≤ C.length) ∧ t % 2 = r % 2 ∧
        (Odd (t + 2) → t + 2 ∈ oddCycleLengths G) ∧
        (Odd (t + 3) → t + 3 ∈ oddCycleLengths G) ∧
        (Odd (t + P.length + 2) → t + P.length + 2 ∈ oddCycleLengths G) := by
  have hA : A ∉ C.support := fun h ↦ Set.disjoint_left.mp hPC P.start_mem_support h
  have hB : B ∉ C.support := fun h ↦ Set.disjoint_left.mp hPC P.end_mem_support h
  have hEdgeC : Disjoint {v | v ∈ hAB.toWalk.support} {v | v ∈ C.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hvC
    have hvAB : v = A ∨ v = B := by simpa using hv
    rcases hvAB with rfl | rfl
    · exact hA hvC
    · exact hB hvC
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE, hlen⟩ :=
      exists_cycle_of_common_attachment hAB.isPath_toWalk hAB.ne hEdgeC hAc hBc
    exact (mem_oddCycleLengths G).mpr ⟨by decide, A, E, hE, by simpa using hlen⟩
  · intro t ht
    obtain ⟨_, hpar, hspec⟩ := complementaryParityDistances_spec D C.length r hC.2.1 hD ht
    obtain ⟨hbound, _, htwo, hthree, hmixed⟩ :=
      shared_edge_attachment_memberships hC hP hPC hAB hAc hBc D hD hAdj hspec
    exact ⟨hbound, hpar, htwo, hthree, hmixed⟩

end JSP000078
