import JSP000078.OddCycleFan
import JSP000078.CyclePositions
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Proper chords at a vertex of a spanning cycle -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- On a spanning cycle, all neighbors other than the two rim neighbors
are proper incident chords, with exact count degree minus two. -/
theorem exists_spanning_cycle_chord_indices [DecidableRel G.Adj]
    {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    (hspan : ∀ v : V, v ∈ C.support) :
    ∃ J : Finset (Fin C.length), J.card + 2 = G.degree c ∧
      ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val) := by
  classical
  let X := (G.neighborFinset c).erase C.snd |>.erase C.penultimate
  have hsnd : C.snd ∈ G.neighborFinset c := by
    exact (G.mem_neighborFinset c C.snd).mpr (C.adj_snd hC.not_nil)
  have hpen : C.penultimate ∈ (G.neighborFinset c).erase C.snd := by
    apply Finset.mem_erase.mpr
    exact ⟨hC.snd_ne_penultimate.symm, (G.mem_neighborFinset c C.penultimate).mpr (C.adj_penultimate hC.not_nil).symm⟩
  have hXcard : X.card + 2 = G.degree c := by
    have h₁ := Finset.card_erase_add_one hsnd
    have h₂ := Finset.card_erase_add_one hpen
    change (((G.neighborFinset c).erase C.snd).erase C.penultimate).card + 2 = _
    rw [← G.card_neighborFinset_eq_degree c]
    omega
  let pos : V → Fin C.length := fun v ↦ ⟨cyclePosition C v, cyclePosition_lt hC (hspan v)⟩
  let J := X.image pos
  have hcard : J.card = X.card := by
    apply Finset.card_image_of_injective
    intro u v h
    exact cyclePosition_injOn C (hspan u) (hspan v) (congrArg Fin.val h)
  refine ⟨J, by omega, ?_⟩
  intro j hj
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hvpen, hvrest⟩ := Finset.mem_erase.mp hv
  obtain ⟨hvsnd, hvN⟩ := Finset.mem_erase.mp hvrest
  have hadj : G.Adj c v := (G.mem_neighborFinset c v).mp hvN
  have hpos := cyclePosition_lt hC (hspan v)
  have hget := getVert_cyclePosition C (hspan v)
  have hp0 : cyclePosition C v ≠ 0 := by
    intro h
    rw [h, Walk.getVert_zero] at hget
    exact hadj.ne hget
  have hp1 : cyclePosition C v ≠ 1 := by
    intro h
    rw [h] at hget
    exact hvsnd hget.symm
  have hplast : cyclePosition C v ≠ C.length - 1 := by
    intro h
    rw [h] at hget
    exact hvpen hget.symm
  refine ⟨by change 2 ≤ cyclePosition C v; omega, ?_, ?_⟩
  · change cyclePosition C v + 2 ≤ C.length
    omega
  · change G.Adj c (C.getVert (cyclePosition C v))
    simpa only [hget] using hadj

end JSP000078
