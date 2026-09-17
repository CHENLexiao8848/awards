import JSP000078.TwoAttachmentOneLength
import JSP000078.RotatedRimNeighbors
import JSP000078.GyarfasLemmaSeven

/-! # The two-attachment boundary with a single odd cycle length -/

namespace JSP000078

open SimpleGraph

/-- Two attachments at each endpoint force two odd lengths, including
the boundary where the selected attachment sets are disjoint. -/
theorem distinct_attachments_impossible_one
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (X Y : Finset V) (hK : (oddCycleLengths G).card = 1) (hXcard : X.card = 2) (hYcard : Y.card = 2)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ G.Adj A v)
    (hY : ∀ v ∈ Y, v ∈ C.support ∧ G.Adj B v) : False := by
  classical
  by_cases hdis : Disjoint X Y
  · obtain ⟨x₁, x₂, hxne, hXeq⟩ := Finset.card_eq_two.mp hXcard
    obtain ⟨y, z, hyz, hYeq⟩ := Finset.card_eq_two.mp hYcard
    have hx₁ : x₁ ∈ X := by simp [hXeq]
    have hx₂ : x₂ ∈ X := by simp [hXeq]
    have hy : y ∈ Y := by simp [hYeq]
    have hz : z ∈ Y := by simp [hYeq]
    have pairAt : ∀ b (hb : b ∈ Y),
        s(x₁, x₂) = s((C.rotate b (hY b hb).1).getVert 1,
          (C.rotate b (hY b hb).1).getVert (C.length - 1)) ∧ 5 ≤ C.length := by
      intro b hb
      let R := C.rotate b (hY b hb).1
      have hR : R.IsCycle := hC.rotate (hY b hb).1
      have hRO : Odd R.length := by simpa only [R, Walk.length_rotate] using hCO
      have hPR : Disjoint {v | v ∈ P.support} {v | v ∈ R.support} := by
        apply Set.disjoint_left.mpr
        intro v hvP hvR
        exact Set.disjoint_left.mp hPC hvP ((C.mem_support_rotate_iff b (hY b hb).1).mp hvR)
      have hx₁R : x₁ ∈ R.support := (C.mem_support_rotate_iff b (hY b hb).1).mpr (hX x₁ hx₁).1
      have hx₂R : x₂ ∈ R.support := (C.mem_support_rotate_iff b (hY b hb).1).mpr (hX x₂ hx₂).1
      have hx₁b : x₁ ≠ b := fun h ↦ Finset.disjoint_left.mp hdis hx₁ (h ▸ hb)
      have hx₂b : x₂ ≠ b := fun h ↦ Finset.disjoint_left.mp hdis hx₂ (h ▸ hb)
      obtain ⟨hpair, _, _, hN⟩ := two_attachment_vertices_one_length hR hRO hP hAB hPR
        (hY b hb).2 hx₁R hx₂R hx₁b hx₂b hxne (hX x₁ hx₁).2 (hX x₂ hx₂).2 hK
      simpa only [R, Walk.length_rotate] using And.intro hpair hN
    have hpairY := pairAt y hy
    have hpairZ := pairAt z hz
    have heq := rotated_rim_neighbors_injective hC hpairY.2 (hY y hy).1 (hY z hz).1
      (hpairY.1.symm.trans hpairZ.1)
    exact hyz heq
  · obtain ⟨x, hx, hy⟩ := Finset.not_disjoint_iff.mp hdis
    have hcount := odd_lengths_of_shared_attachment hC hCO hP hAB hPC X 1
      (by decide) hXcard hX hx (hY x hy).2
    omega

end JSP000078
