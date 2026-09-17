import JSP000078.CommonAttachmentCount
import JSP000078.CommonAttachmentGeometry
import JSP000078.ComplementaryParitySelection

/-! # Counting odd cycles from a shared attachment and many first-endpoint spokes -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Choose arc orientation so all selected lengths have the useful parity.
The second outside endpoint need only meet the common base vertex. -/
theorem odd_lengths_of_many_common_base_spokes {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hAc : G.Adj A c) (hBc : G.Adj B c)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 1 ≤ d ∧ d < C.length ∧ G.Adj A (C.getVert d))
    (k : ℕ) (hk : 1 ≤ k) (hcard : 2 * k - 1 ≤ D.card) :
    k + 1 ≤ (oddCycleLengths G).card := by
  have hs : 1 ≤ P.length := Nat.pos_of_ne_zero fun h ↦ hAB (Walk.eq_of_length_eq_zero h)
  let parity := P.length + 1
  obtain ⟨T, hTcard, hTspec⟩ := exists_complementary_distances_of_parity
    D C.length parity k hCO hk (fun d hd ↦ ⟨(hD d hd).1, (hD d hd).2.1⟩) hcard
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hMembers : ∀ t ∈ T,
      (Odd (t + 2) → t + 2 ∈ oddCycleLengths G) ∧
      (Odd (t + P.length + 2) → t + P.length + 2 ∈ oddCycleLengths G) := by
    intro t ht
    rcases (hTspec t ht).2.2 with htD | ⟨d, hd, rfl⟩
    · have hmem := common_attachment_cycle_memberships hC hP hAB hPC
        (hD t htD).1 (hD t htD).2.1 hAc hBc (hD t htD).2.2
      exact ⟨hmem.1, fun ho ↦ by
        simpa only [Nat.add_comm t P.length] using hmem.2.2.1
          (by simpa only [Nat.add_comm t P.length] using ho)⟩
    · have hmem := common_attachment_cycle_memberships hC hP hAB hPC
        (hD d hd).1 (hD d hd).2.1 hAc hBc (hD d hd).2.2
      exact ⟨hmem.2.1, fun ho ↦ by
        simpa only [Nat.add_comm (C.length - d) P.length] using hmem.2.2.2.1
          (by simpa only [Nat.add_comm (C.length - d) P.length] using ho)⟩
  let E : CommonAttachmentData := {
    oddLengths := oddCycleLengths G
    pathLength := P.length
    path_pos := hs
    arcLengths := T
    arc_nonempty := hTne
    arc_pos := fun t ht ↦ (hTspec t ht).1.1
    direct := fun t ht ↦ (hMembers t ht).1
    mixed := fun t ht ↦ (hMembers t ht).2
    shared := by
      intro ho
      obtain ⟨Q, hQ, hQL⟩ := exists_cycle_of_common_attachment hP hAB hPC hAc hBc
      exact (mem_oddCycleLengths G).mpr ⟨ho, A, Q, hQ, hQL⟩ }
  have hcount : T.card + 1 ≤ (oddCycleLengths G).card := by
    rcases Nat.even_or_odd P.length with hEven | hOdd
    · apply E.count_of_even_path hEven
      intro t ht
      have hpar := (hTspec t ht).2.1
      have hspar := Nat.even_iff.mp hEven
      change t % 2 = (P.length + 1) % 2 at hpar
      rw [Nat.odd_iff]
      omega
    · apply E.count_of_odd_path hOdd
      intro t ht
      have hpar := (hTspec t ht).2.1
      have hspar := Nat.odd_iff.mp hOdd
      change t % 2 = (P.length + 1) % 2 at hpar
      rw [Nat.even_iff]
      omega
  omega

end JSP000078
