import JSP000078.OutsideVertexCycles
import JSP000078.AttachmentCycles

/-!
# Cycles from common attachments of an outside path

A shared cycle neighbor closes the outside path by two edges. A second
shared neighbor supplies both one-vertex spoke cycles and mixed cycles
through the entire outside path, on either complementary cycle arc.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A common cycle neighbor of the two outside-path endpoints gives a
simple cycle whose length is the outside-path length plus two. -/
theorem exists_cycle_of_common_attachment {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B}
    (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hAc : G.Adj A c) (hBc : G.Adj B c) :
    ∃ E : G.Walk A A, E.IsCycle ∧ E.length = P.length + 2 := by
  have hnilC : ∀ v ∈ (Walk.nil : G.Walk c c).support, v ∈ C.support := by
    intro v hv
    have heq : v = c := by simpa using hv
    exact heq ▸ C.start_mem_support
  obtain ⟨E, hE, hlen⟩ := exists_cycle_of_outside_path_and_cycle_arc
    hP Walk.IsPath.nil hAB hPC hnilC hAc hBc
  exact ⟨E, hE, by simpa only [Walk.length_nil, Nat.add_zero] using hlen⟩

/-- Two common attachment positions produce four simple cycles: both
arc cycles through the first endpoint, and both arc cycles through the
whole outside path. The base attachment also gives a fifth cycle. -/
theorem exists_common_attachment_cycles {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B} {t : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (htpos : 1 ≤ t) (htN : t < C.length)
    (hAc : G.Adj A c) (hBc : G.Adj B c) (hAt : G.Adj A (C.getVert t)) :
    ∃ E₁ E₂ E₃ E₄ E₀ : G.Walk A A,
      E₁.IsCycle ∧ E₂.IsCycle ∧ E₃.IsCycle ∧ E₄.IsCycle ∧ E₀.IsCycle ∧
      E₁.length = t + 2 ∧ E₂.length = C.length - t + 2 ∧
      E₃.length = P.length + t + 2 ∧
      E₄.length = P.length + (C.length - t) + 2 ∧ E₀.length = P.length + 2 := by
  have hAC : A ∉ C.support := fun h ↦ Set.disjoint_left.mp hPC P.start_mem_support h
  obtain ⟨E₁, E₂, hE₁, hE₂, hL₁, hL₂⟩ :=
    exists_cycles_of_outside_vertex_at_index hC hAC htpos htN hAc hAt
  obtain ⟨E₃, E₄, hE₃, hE₄, hL₃, hL₄⟩ :=
    exists_attachment_cycles_at_index hP hAB hC hPC htpos htN hAt hBc
  obtain ⟨E₀, hE₀, hL₀⟩ := exists_cycle_of_common_attachment hP hAB hPC hAc hBc
  exact ⟨E₁, E₂, E₃, E₄, E₀, hE₁, hE₂, hE₃, hE₄, hE₀, hL₁, hL₂, hL₃, hL₄, hL₀⟩

/-- Oddness of any of the five common-attachment lengths supplies
membership in the finite set of actual odd simple-cycle lengths. -/
theorem common_attachment_cycle_memberships [Fintype V] {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B} {t : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (htpos : 1 ≤ t) (htN : t < C.length)
    (hAc : G.Adj A c) (hBc : G.Adj B c) (hAt : G.Adj A (C.getVert t)) :
    (Odd (t + 2) → t + 2 ∈ oddCycleLengths G) ∧
    (Odd (C.length - t + 2) → C.length - t + 2 ∈ oddCycleLengths G) ∧
    (Odd (P.length + t + 2) → P.length + t + 2 ∈ oddCycleLengths G) ∧
    (Odd (P.length + (C.length - t) + 2) →
      P.length + (C.length - t) + 2 ∈ oddCycleLengths G) ∧
    (Odd (P.length + 2) → P.length + 2 ∈ oddCycleLengths G) := by
  obtain ⟨E₁, E₂, E₃, E₄, E₀, hE₁, hE₂, hE₃, hE₄, hE₀, hL₁, hL₂, hL₃, hL₄, hL₀⟩ :=
    exists_common_attachment_cycles hC hP hAB hPC htpos htN hAc hBc hAt
  exact ⟨fun h ↦ (mem_oddCycleLengths G).mpr ⟨h, A, E₁, hE₁, hL₁⟩,
    fun h ↦ (mem_oddCycleLengths G).mpr ⟨h, A, E₂, hE₂, hL₂⟩,
    fun h ↦ (mem_oddCycleLengths G).mpr ⟨h, A, E₃, hE₃, hL₃⟩,
    fun h ↦ (mem_oddCycleLengths G).mpr ⟨h, A, E₄, hE₄, hL₄⟩,
    fun h ↦ (mem_oddCycleLengths G).mpr ⟨h, A, E₀, hE₀, hL₀⟩⟩

end JSP000078
