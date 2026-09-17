import JSP000078.HistoricalCountingSpec

/-!
# Exact incident-chord fans inside an ambient graph

Restricting to a cycle and selected incident chords gives the exact graph
needed by the bipartiteness alternative. The final graph uses the cycle
support as its vertex type and has an injective homomorphism to the ambient
graph, without requiring its image to be induced.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An exact fan on a spanning cycle, obtained by keeping only its rim
and the selected incident chords. -/
theorem exists_cycle_fan_of_spanning_indices {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hspan : ∀ v : V, v ∈ C.support)
    (J : Finset (Fin C.length))
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) :
    ∃ (H : SimpleGraph V) (F : CycleWithIncidentChords H),
      H ≤ G ∧ F.cycle.length = C.length ∧ F.indices.card = J.card ∧
        F.indices.image (fun j ↦ j.val) = J.image (fun j ↦ j.val) := by
  classical
  let H : SimpleGraph V := {
    Adj := fun u v ↦ G.Adj u v ∧
      (s(u, v) ∈ C.edges ∨ ∃ j ∈ J, s(u, v) = s(c, C.getVert j.val))
    symm.symm := by
      intro u v h
      refine ⟨h.1.symm, ?_⟩
      simpa only [Sym2.eq_swap] using h.2
    loopless.irrefl := by intro u h; exact G.loopless.irrefl u h.1
  }
  have hHG : H ≤ G := fun _ _ h ↦ h.1
  have hCE : ∀ e, e ∈ C.edges → e ∈ H.edgeSet := by
    intro e he
    induction e using Sym2.ind with | _ u v =>
      exact ⟨C.adj_of_mem_edges he, Or.inl he⟩
  let D := C.transfer H hCE
  have hD : D.IsCycle := hC.transfer hCE
  have hDlen : D.length = C.length := C.length_transfer hCE
  have hDsupport : D.support = C.support := C.support_transfer hCE
  have hDedges : D.edges = C.edges := C.edges_transfer hCE
  have hDget (i : ℕ) : D.getVert i = C.getVert i := by
    have hmap : D.mapLe hHG = C := by
      apply Walk.ext_support
      simpa only [Walk.support_mapLe_eq_support] using hDsupport
    have heq := congrArg (fun W : G.Walk c c ↦ W.getVert i) hmap
    simpa using heq
  let f : Fin C.length → Fin D.length := fun j ↦ ⟨j.val, hDlen.symm ▸ j.isLt⟩
  let J' := J.image f
  have hJ'card : J'.card = J.card := by
    apply Finset.card_image_of_injective
    intro i j h
    apply Fin.ext
    exact congrArg (fun z : Fin D.length ↦ z.val) h
  let F : CycleWithIncidentChords H := {
    base := c
    cycle := D
    isCycle := hD
    indices := J'
    proper_indices := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨(hJ i hi).1, by simpa only [f, hDlen] using (hJ i hi).2.1⟩
    chord_adj := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      change H.Adj c (D.getVert i.val)
      rw [hDget]
      exact ⟨(hJ i hi).2.2, Or.inr ⟨i, hi, rfl⟩⟩
    spanning := by intro v; rw [hDsupport]; exact hspan v
    edge_exact := by
      intro u v
      constructor
      · intro h
        rcases h.2 with he | ⟨j, hj, he⟩
        · exact Or.inl (hDedges.symm ▸ he)
        · right
          refine ⟨f j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
          simpa only [f, hDget] using he
      · intro h
        rcases h with he | ⟨j, hj, he⟩
        · have heC : s(u, v) ∈ C.edges := hDedges ▸ he
          exact ⟨C.adj_of_mem_edges heC, Or.inl heC⟩
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          have heC : s(u, v) = s(c, C.getVert i.val) := by simpa only [f, hDget] using he
          refine ⟨?_, Or.inr ⟨i, hi, heC⟩⟩
          have hedge : s(c, C.getVert i.val) ∈ G.edgeSet := (hJ i hi).2.2
          change s(u, v) ∈ G.edgeSet
          rw [heC]
          exact hedge
  }
  refine ⟨H, F, hHG, hDlen, hJ'card, ?_⟩
  change (J.image f).image (fun j ↦ j.val) = J.image (fun j ↦ j.val)
  rw [Finset.image_image]
  rfl

/-- The basic exact-fan interface, without the additional chord-index
image identity. -/
theorem exists_cycle_fan_of_spanning {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hspan : ∀ v : V, v ∈ C.support)
    (J : Finset (Fin C.length))
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) :
    ∃ (H : SimpleGraph V) (F : CycleWithIncidentChords H),
      H ≤ G ∧ F.cycle.length = C.length ∧ F.indices.card = J.card := by
  obtain ⟨H, F, hHG, hlen, hcard, _⟩ := exists_cycle_fan_of_spanning_indices hC hspan J hJ
  exact ⟨H, F, hHG, hlen, hcard⟩

/-- Any ambient cycle with selected proper incident chords contains an
exact fan on its support subtype, with the same cycle length and chord
count. The selected graph is a subgraph of the induced ambient graph. -/
theorem exists_cycle_fan_on_support_indices {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (J : Finset (Fin C.length))
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) :
    ∃ (H : SimpleGraph {v : V // v ∈ C.support}) (F : CycleWithIncidentChords H),
      H ≤ G.induce {v | v ∈ C.support} ∧
        F.cycle.length = C.length ∧ F.indices.card = J.card ∧
          F.indices.image (fun j ↦ j.val) = J.image (fun j ↦ j.val) := by
  classical
  let S : Set V := {v | v ∈ C.support}
  let D := C.induce S (fun _ hv ↦ hv)
  let f := (SimpleGraph.Embedding.induce S (G := G)).toHom
  have hmap : D.map f = C := C.map_induce _
  have hD : D.IsCycle := Walk.IsCycle.of_map (hmap.symm ▸ hC)
  have hDlen : D.length = C.length := by
    calc
      D.length = (D.map f).length := (Walk.length_map f D).symm
      _ = C.length := congrArg (fun W : G.Walk c c ↦ W.length) hmap
  have hDget (i : ℕ) : (D.getVert i).val = C.getVert i := by
    calc
      (D.getVert i).val = (D.map f).getVert i := (Walk.getVert_map f D i).symm
      _ = C.getVert i := congrArg (fun W : G.Walk c c ↦ W.getVert i) hmap
  have hspan : ∀ v : S, v ∈ D.support := by
    intro v
    have hv : v.val ∈ (D.map f).support := hmap.symm ▸ v.property
    rw [Walk.support_map] at hv
    obtain ⟨w, hw, hweq⟩ := List.mem_map.mp hv
    have hwv : w = v := Subtype.ext hweq
    exact hwv ▸ hw
  let idx : Fin C.length → Fin D.length := fun j ↦ ⟨j.val, hDlen.symm ▸ j.isLt⟩
  let J' := J.image idx
  have hJcard : J'.card = J.card := by
    apply Finset.card_image_of_injective
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin D.length ↦ z.val) h)
  have hJ' : ∀ j ∈ J', 2 ≤ j.val ∧ j.val + 2 ≤ D.length ∧
      (G.induce S).Adj ⟨c, C.start_mem_support⟩ (D.getVert j.val) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨(hJ i hi).1, by simpa only [idx, hDlen] using (hJ i hi).2.1, ?_⟩
    change G.Adj c ((D.getVert i.val).val)
    rw [hDget]
    exact (hJ i hi).2.2
  obtain ⟨H, F, hHG, hFL, hFJ, hFidx⟩ := exists_cycle_fan_of_spanning_indices hD hspan J' hJ'
  refine ⟨H, F, hHG, hFL.trans hDlen, hFJ.trans hJcard, ?_⟩
  rw [hFidx]
  change (J.image idx).image (fun j ↦ j.val) = J.image (fun j ↦ j.val)
  rw [Finset.image_image]
  rfl

/-- Basic support-subtype fan construction, retaining its original
interface while the stronger variant also preserves exact chord positions. -/
theorem exists_cycle_fan_on_support {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (J : Finset (Fin C.length))
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) :
    ∃ (H : SimpleGraph {v : V // v ∈ C.support}) (F : CycleWithIncidentChords H),
      H ≤ G.induce {v | v ∈ C.support} ∧
        F.cycle.length = C.length ∧ F.indices.card = J.card := by
  obtain ⟨H, F, hHG, hlen, hcard, _⟩ := exists_cycle_fan_on_support_indices hC J hJ
  exact ⟨H, F, hHG, hlen, hcard⟩

end JSP000078
