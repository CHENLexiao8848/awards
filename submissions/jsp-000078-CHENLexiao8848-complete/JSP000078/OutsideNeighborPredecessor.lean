import JSP000078.OutsideVertexCycles
import JSP000078.SpokeParityExhaustion
import JSP000078.EndpointConfigurationBridge

/-! # Saturated outside-neighbor sets contain the two-step predecessor -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- If a vertex outside an odd cycle has 2k+1 selected neighbors on that
cycle while only k odd lengths occur, every selected neighbor sees its
two-step predecessor in the same selected set. -/
theorem outside_neighbors_predecessor_mem {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hv : v ∉ C.support)
    (k : ℕ) (hK : (oddCycleLengths G).card = k) (X : Finset V)
    (hcard : X.card = 2 * k + 1)
    (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj v x)
    {x : V} (hx : x ∈ X) :
    (C.rotate x (hX x hx).1).getVert (C.length - 2) ∈ X := by
  classical
  let R := C.rotate x (hX x hx).1
  have hR : R.IsCycle := hC.rotate (hX x hx).1
  have hRlen : R.length = C.length := C.length_rotate x (hX x hx).1
  have hvR : v ∉ R.support := fun h ↦ hv ((C.mem_support_rotate_iff x (hX x hx).1).mp h)
  let D := (X.erase x).image (cyclePosition R)
  have hDcard : D.card = 2 * k := by
    have hinj : Set.InjOn (cyclePosition R) (X.erase x) := by
      intro a ha b hb hab
      apply cyclePosition_injOn R _ _ hab
      · exact (C.mem_support_rotate_iff x (hX x hx).1).mpr (hX a (Finset.mem_of_mem_erase ha)).1
      · exact (C.mem_support_rotate_iff x (hX x hx).1).mpr (hX b (Finset.mem_of_mem_erase hb)).1
    change ((X.erase x).image (cyclePosition R)).card = 2 * k
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hx, hcard]
    omega
  have hbound : ∀ d ∈ D, 1 ≤ d ∧ d < R.length := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hax, haX⟩ := Finset.mem_erase.mp ha
    have haR := (C.mem_support_rotate_iff x (hX x hx).1).mpr (hX a haX).1
    exact ⟨(cyclePosition_pos_iff R haR).mpr hax, cyclePosition_lt hR haR⟩
  have hAdj : ∀ d ∈ D, G.Adj v (R.getVert d) := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    have haX := Finset.mem_of_mem_erase ha
    have haR := (C.mem_support_rotate_iff x (hX x hx).1).mpr (hX a haX).1
    rw [getVert_cyclePosition R haR]
    exact (hX a haX).2
  have hNmem : R.length ∈ oddCycleLengths G :=
    (mem_oddCycleLengths G).mpr ⟨hRlen ▸ hCO, x, R, hR, rfl⟩
  have hdmem := (sub_two_mem_of_spoke_parity_exhaustion D (oddCycleLengths G)
    R.length k hDcard hK hbound hNmem
    (fun d hd ho ↦ outside_vertex_forward_length_mem hR hvR
      (hbound d hd).1 (hbound d hd).2 (hX x hx).2 (hAdj d hd) (ho.add_even even_two))
    (fun d hd he ↦ outside_vertex_complement_length_mem hR hvR
      (hbound d hd).1 (hbound d hd).2 (hX x hx).2 (hAdj d hd) (by
        have hn := Nat.odd_iff.mp (hRlen ▸ hCO : Odd R.length)
        have hdB := (hbound d hd).2
        have heven := Nat.even_iff.mp (Nat.not_odd_iff_even.mp he)
        rw [Nat.odd_iff]
        omega))).1
  obtain ⟨a, ha, hapos⟩ := Finset.mem_image.mp hdmem
  have haX := Finset.mem_of_mem_erase ha
  have haR := (C.mem_support_rotate_iff x (hX x hx).1).mpr (hX a haX).1
  have heq : R.getVert (C.length - 2) = a := by
    rw [← hRlen, ← hapos, getVert_cyclePosition R haR]
  exact heq ▸ haX

end JSP000078
