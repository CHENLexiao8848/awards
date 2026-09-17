import JSP000078.AttachmentCycles
import JSP000078.LongestOddCycle

/-!
# A shared endpoint edge forbids neighboring cycle attachments

If two outside vertices are adjacent, their three-edge route between
shared cycle neighbors would extend the complementary arc between two
consecutive cycle vertices to a longer odd cycle.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An outside edge with attachments to the base and position `d` of a
longest odd cycle cannot use either position neighboring the base. -/
theorem common_edge_attachment_positions_not_near_base {c A B : V}
    {C : G.Walk c c} (hC : IsLongestOddCycle C)
    (hA : A ∉ C.support) (hB : B ∉ C.support) (hAB : G.Adj A B)
    {d : ℕ} (hdpos : 1 ≤ d) (hdN : d < C.length)
    (hAd : G.Adj A (C.getVert d)) (hBc : G.Adj B c) :
    2 ≤ d ∧ d + 2 ≤ C.length := by
  have hPC : Disjoint {v | v ∈ hAB.toWalk.support} {v | v ∈ C.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hvC
    have hvAB : v = A ∨ v = B := by simpa using hv
    rcases hvAB with rfl | rfl
    · exact hA hvC
    · exact hB hvC
  obtain ⟨E, F, hE, hF, hElen, hFlen⟩ := exists_attachment_cycles_at_index
    hAB.isPath_toWalk hAB.ne hC.1 hPC hdpos hdN hAd hBc
  have hplen : hAB.toWalk.length = 1 := by simp
  have hdne : d ≠ 1 := by
    intro hd
    have hFlong : F.length = C.length + 2 := by
      rw [hplen, hd] at hFlen
      omega
    have hFO : Odd F.length := by rw [hFlong]; exact hC.2.1.add_even even_two
    have hmax := hC.2.2 A F hF hFO
    omega
  have hdlast : d + 1 ≠ C.length := by
    intro hd
    have hElong : E.length = C.length + 2 := by
      rw [hplen] at hElen
      omega
    have hEO : Odd E.length := by rw [hElong]; exact hC.2.1.add_even even_two
    have hmax := hC.2.2 A E hE hEO
    omega
  exact ⟨by omega, by omega⟩

end JSP000078
