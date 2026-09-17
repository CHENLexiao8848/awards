import JSP000078.TwoEndpointChordPaths
import JSP000078.TwoChordLengthClassification

/-!
# Classified route families from two distinct endpoint chords

The four explicit routes supply enough length values for the connector
argument. No assertion classifies every possible path in the ambient graph.
The shared endpoint edge is excluded and handled by its separate theorem.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two proper endpoint chords, without an endpoint edge, give a finite
family of supported simple routes with at least three lengths or one of
the two crossing exceptional length sets. -/
theorem exists_classified_two_chord_routes {A B : V} {P : G.Walk A B}
    (hP : P.IsPath) (hAB : ¬G.Adj A B) {i j : ℕ}
    (hi : 2 ≤ i) (hiL : i ≤ P.length) (hj : j + 2 ≤ P.length)
    (hAi : G.Adj A (P.getVert i)) (hBj : G.Adj B (P.getVert j)) :
    ∃ R : Finset ℕ,
      (∀ h ∈ R, ∃ Q : G.Walk A B, Q.IsPath ∧ Q.length = h ∧ Q.support ⊆ P.support) ∧
      (∀ h ∈ R, 1 ≤ h) ∧
      (3 ≤ R.card ∨ (∃ β : ℕ, 1 ≤ β ∧ R = {β + 2, 3 * β + 2}) ∨
        ∃ β : ℕ, 1 ≤ β ∧ R = {2, β + 2}) := by
  have hiLt : i < P.length := by
    by_contra h
    have hieq : i = P.length := by omega
    exact hAB (by simpa only [hieq, Walk.getVert_length] using hAi)
  have hjPos : 1 ≤ j := by
    by_contra h
    have hjzero : j = 0 := by omega
    apply hAB
    simpa only [hjzero, Walk.getVert_zero] using hBj.symm
  have hends : A ≠ B := by
    intro heq
    have hnil := hP.nil_iff_eq.mpr heq
    have hzero := hnil.length_eq_zero
    omega
  have horiginal : ∃ Q : G.Walk A B, Q.IsPath ∧ Q.length = P.length ∧ Q.support ⊆ P.support :=
    ⟨P, hP, rfl, fun _ hv ↦ hv⟩
  have hstart := exists_path_of_path_start_spoke_support_subset hP (show 1 ≤ i by omega) hiL hAi
  have hend := exists_path_of_path_end_spoke_support_subset hP (show j < P.length by omega) hBj
  have hpositive (R : Finset ℕ)
      (hreal : ∀ h ∈ R, ∃ Q : G.Walk A B, Q.IsPath ∧ Q.length = h ∧ Q.support ⊆ P.support) :
      ∀ h ∈ R, 1 ≤ h := by
    intro h hh
    obtain ⟨Q, _, hQlen, _⟩ := hreal h hh
    have hQpos : 0 < Q.length := Nat.pos_of_ne_zero fun hz ↦ hends (Walk.eq_of_length_eq_zero hz)
    omega
  by_cases hij : i ≤ j
  · let R := noncrossingChordLengths P.length i j
    have hboth := exists_path_of_two_endpoint_chords_noncrossing hP
      (show 1 ≤ i by omega) hij (show j < P.length by omega) hAi hBj
    have hreal : ∀ h ∈ R, ∃ Q : G.Walk A B, Q.IsPath ∧ Q.length = h ∧ Q.support ⊆ P.support := by
      intro h hh
      have hcases : h = P.length ∨ h = P.length - i + 1 ∨ h = j + 1 ∨ h = j - i + 2 := by
        simpa only [R, noncrossingChordLengths, Finset.mem_insert, Finset.mem_singleton] using hh
      rcases hcases with rfl | rfl | rfl | rfl
      · exact horiginal
      · exact hstart
      · exact hend
      · exact hboth
    exact ⟨R, hreal, hpositive R hreal, Or.inl (three_le_card_noncrossingChordLengths hi hij hj)⟩
  · have hji : j < i := by omega
    let R := crossingChordLengths P.length i j
    have hboth := exists_path_of_two_endpoint_chords_crossing hP hjPos hji hiLt hAi hBj
    have hreal : ∀ h ∈ R, ∃ Q : G.Walk A B, Q.IsPath ∧ Q.length = h ∧ Q.support ⊆ P.support := by
      intro h hh
      have hcases : h = P.length ∨ h = P.length - i + 1 ∨ h = j + 1 ∨ h = i - j + 2 := by
        simpa only [R, crossingChordLengths, Finset.mem_insert, Finset.mem_singleton] using hh
      rcases hcases with rfl | rfl | rfl | rfl
      · exact horiginal
      · exact hstart
      · exact hend
      · exact hboth
    refine ⟨R, hreal, hpositive R hreal, ?_⟩
    rcases crossingChordLengths_three_or_exception hjPos hji hiLt with hcard | hfirst | hsecond
    · exact Or.inl hcard
    · exact Or.inr (Or.inl ⟨i - j, by omega, hfirst⟩)
    · exact Or.inr (Or.inr ⟨i - j, by omega, hsecond⟩)

end JSP000078
