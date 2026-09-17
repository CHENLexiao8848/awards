import JSP000078.SharedAttachmentCycle
import JSP000078.FanSubgraph

/-!
# An exact fan on an outside path and its shared attachment

Many proper initial chords of the path remain proper after the two
attachment edges are appended. Selecting the required number produces
the exact cycle-and-chords graph used in the singleton-neighbor case.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Select an exact `2*k-1` chord fan on the concrete cycle formed by
an outside path and one common attachment. The base cycle need not be even. -/
theorem exists_fan_on_shared_attachment_cycle {A B x : V} {P : G.Walk A B}
    (hP : P.IsPath) (hAB : A ≠ B) (hxP : x ∉ P.support)
    (hAx : G.Adj A x) (hBx : G.Adj B x)
    (S : Finset ℕ) (k : ℕ) (hcard : 2 * k - 1 ≤ S.card)
    (hS : ∀ i ∈ S, 2 ≤ i ∧ i ≤ P.length ∧ G.Adj A (P.getVert i)) :
    let D := (P.concat hBx).concat hAx.symm
    ∃ (H : SimpleGraph {v : V // v ∈ D.support}) (F : CycleWithIncidentChords H),
      H ≤ G.induce {v | v ∈ D.support} ∧ F.cycle.length = P.length + 2 ∧
        F.indices.card = 2 * k - 1 := by
  classical
  let D := (P.concat hBx).concat hAx.symm
  have hD : D.IsCycle := shared_attachment_cycle_isCycle hP hAB hxP hAx hBx
  have hDlen : D.length = P.length + 2 := shared_attachment_cycle_length P hAx hBx
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
  let idx (i : {i : ℕ // i ∈ T}) : Fin D.length :=
    ⟨i.val, by have := (hS i.val (hTS i.property)).2.1; omega⟩
  let J : Finset (Fin D.length) := T.attach.image idx
  have hJcard : J.card = 2 * k - 1 := by
    change (T.attach.image idx).card = _
    rw [Finset.card_image_of_injective]
    · simpa only [Finset.card_attach] using hTcard
    · intro i j heq
      apply Subtype.ext
      exact congrArg (fun q : Fin D.length ↦ q.val) heq
  have hJ : ∀ i ∈ J, 2 ≤ i.val ∧ i.val + 2 ≤ D.length ∧ G.Adj A (D.getVert i.val) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hj2, hjL, hAj⟩ := hS j.val (hTS j.property)
    exact shared_attachment_cycle_chord P hAx hBx hj2 hjL hAj
  obtain ⟨H, F, hHG, hFL, hFcard⟩ := exists_cycle_fan_on_support hD J hJ
  exact ⟨H, F, hHG, hFL.trans hDlen, hFcard.trans hJcard⟩

end JSP000078
