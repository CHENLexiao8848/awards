import JSP000078.OneHubPairRigidity
import JSP000078.AttachmentCycles
import JSP000078.TwoSpokeCycle
import JSP000078.CycleSegments
import JSP000078.CyclePositions
import JSP000078.Basic

/-!
# Two attachments when only one odd cycle length occurs

Two ordered attachments of one outside endpoint, together with a cycle
attachment of the other endpoint, determine both attachment positions and
the parity and length of the outside path.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Ordered cycle indices satisfy the one-length hub rigidity conclusion
when all its membership hypotheses come from the actual attachment cycles. -/
theorem two_attachment_indices_one_length {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B} (hC : C.IsCycle) (hCO : Odd C.length)
    (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hBc : G.Adj B c) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b < C.length)
    (hAa : G.Adj A (C.getVert a)) (hAb : G.Adj A (C.getVert b))
    (hK : (oddCycleLengths G).card = 1) :
    a = 1 ∧ b = C.length - 1 ∧ Even P.length ∧ P.length + 3 = C.length ∧ 5 ≤ C.length := by
  have hL : 1 ≤ P.length :=
    Nat.pos_of_ne_zero fun h ↦ hAB (Walk.eq_of_length_eq_zero h)
  have hNmem : C.length ∈ oddCycleLengths G :=
    (mem_oddCycleLengths G).mpr ⟨hCO, c, C, hC, rfl⟩
  have hmixed (t : ℕ) (htpos : 1 ≤ t) (htN : t < C.length) (hAt : G.Adj A (C.getVert t)) :
      (Odd (P.length + t + 2) → P.length + t + 2 ∈ oddCycleLengths G) ∧
      (Odd (P.length + (C.length - t) + 2) → P.length + (C.length - t) + 2 ∈ oddCycleLengths G) := by
    obtain ⟨E, F, hE, hF, hEL, hFL⟩ :=
      exists_attachment_cycles_at_index hP hAB hC hPC htpos htN hAt hBc
    exact ⟨fun h ↦ (mem_oddCycleLengths G).mpr ⟨h, A, E, hE, hEL⟩,
      fun h ↦ (mem_oddCycleLengths G).mpr ⟨h, A, F, hF, hFL⟩⟩
  have hspoke : Odd (b - a + 2) → b - a + 2 ∈ oddCycleLengths G := by
    intro hodd
    obtain ⟨q, hq, hqlen, hqsup⟩ := exists_cycle_segment hC hab.le hb
    have hAq : A ∉ q.support := by
      intro hA
      obtain ⟨n, _, _, hn⟩ := (hqsup A).mp hA
      exact Set.disjoint_left.mp hPC P.start_mem_support (hn ▸ C.getVert_mem_support n)
    obtain ⟨E, hE, hEL⟩ := exists_cycle_of_path_two_spokes hq hAq hAa hAb (by omega)
    exact (mem_oddCycleLengths G).mpr ⟨hodd, A, E, hE, by omega⟩
  have haN : a < C.length := by omega
  have hbpos : 1 ≤ b := by omega
  exact one_hub_pair_rigidity (oddCycleLengths G) C.length P.length a b hCO hL ha hab hb hK hNmem
    (hmixed a ha haN hAa).1 (hmixed a ha haN hAa).2
    (hmixed b hbpos hb hAb).1 (hmixed b hbpos hb hAb).2 hspoke

/-- With one odd cycle length, two distinct attachments of the first
outside endpoint must be exactly the two rim neighbors of the second
endpoint's cycle attachment. -/
theorem two_attachment_vertices_one_length {c A B x₁ x₂ : V}
    {C : G.Walk c c} {P : G.Walk A B} (hC : C.IsCycle) (hCO : Odd C.length)
    (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hBc : G.Adj B c)
    (hx₁ : x₁ ∈ C.support) (hx₂ : x₂ ∈ C.support)
    (hx₁c : x₁ ≠ c) (hx₂c : x₂ ≠ c) (hxne : x₁ ≠ x₂)
    (hAx₁ : G.Adj A x₁) (hAx₂ : G.Adj A x₂)
    (hK : (oddCycleLengths G).card = 1) :
    s(x₁, x₂) = s(C.getVert 1, C.getVert (C.length - 1)) ∧
      Even P.length ∧ P.length + 3 = C.length ∧ 5 ≤ C.length := by
  let a := cyclePosition C x₁
  let b := cyclePosition C x₂
  have ha : 1 ≤ a := (cyclePosition_pos_iff C hx₁).mpr hx₁c
  have hb : 1 ≤ b := (cyclePosition_pos_iff C hx₂).mpr hx₂c
  have haN : a < C.length := cyclePosition_lt hC hx₁
  have hbN : b < C.length := cyclePosition_lt hC hx₂
  have hax : C.getVert a = x₁ := getVert_cyclePosition C hx₁
  have hbx : C.getVert b = x₂ := getVert_cyclePosition C hx₂
  have habne : a ≠ b := by
    intro h
    exact hxne (hax.symm.trans ((congrArg C.getVert h).trans hbx))
  have hAa : G.Adj A (C.getVert a) := hax.symm ▸ hAx₁
  have hAb : G.Adj A (C.getVert b) := hbx.symm ▸ hAx₂
  rcases lt_or_gt_of_ne habne with hab | hba
  · obtain ⟨haone, hblast, heven, hlen, hN⟩ :=
      two_attachment_indices_one_length hC hCO hP hAB hPC hBc ha hab hbN hAa hAb hK
    refine ⟨Sym2.eq_iff.mpr (Or.inl ⟨?_, ?_⟩), heven, hlen, hN⟩
    · simpa only [haone] using hax.symm
    · simpa only [hblast] using hbx.symm
  · obtain ⟨hbone, halast, heven, hlen, hN⟩ :=
      two_attachment_indices_one_length hC hCO hP hAB hPC hBc hb hba haN hAb hAa hK
    refine ⟨Sym2.eq_iff.mpr (Or.inr ⟨?_, ?_⟩), heven, hlen, hN⟩
    · simpa only [halast] using hax.symm
    · simpa only [hbone] using hbx.symm

end JSP000078
