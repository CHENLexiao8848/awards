import JSP000078.CycleArcs

/-!
# Cycles formed from an outside path and an attached cycle arc

The two attachment edges contribute two to each cycle length. The two
complementary arc constructions therefore use both original attachments
twice in their combined lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two disjoint simple paths, joined at their respective endpoints by
two edges, form a simple cycle. The outside path is required nontrivial. -/
theorem exists_cycle_of_disjoint_paths_and_attachments {A B x y : V}
    {P : G.Walk A B} {U : G.Walk x y}
    (hP : P.IsPath) (hU : U.IsPath) (hAB : A ≠ B)
    (hPU : Disjoint {v | v ∈ P.support} {v | v ∈ U.support})
    (hAx : G.Adj A x) (hBy : G.Adj B y) :
    ∃ E : G.Walk A A, E.IsCycle ∧ E.length = P.length + U.length + 2 := by
  have hAU : A ∉ U.support := fun hA ↦
    Set.disjoint_left.mp hPU P.start_mem_support hA
  have hBU : B ∉ U.support := fun hB ↦
    Set.disjoint_left.mp hPU P.end_mem_support hB
  let Q : G.Walk A B := .cons hAx (U.concat hBy.symm)
  have hQ : Q.IsPath := by
    apply (hU.concat hBU hBy.symm).cons
    simpa only [Walk.support_concat, List.mem_append, List.mem_singleton, not_or] using
      And.intro hAU hAB
  have hinter : ∀ v ∈ P.support, v ∈ Q.support → v = A ∨ v = B := by
    intro v hvP hvQ
    have hv : v = A ∨ v ∈ U.support ∨ v = B := by
      simpa only [Q, Walk.support_cons, List.mem_cons, Walk.support_concat,
        List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] using hvQ
    rcases hv with hvA | hvU | hvB
    · exact Or.inl hvA
    · exact (Set.disjoint_left.mp hPU hvP hvU).elim
    · exact Or.inr hvB
  have hPlen : 0 < P.length :=
    Nat.pos_of_ne_zero fun h ↦ hAB (Walk.eq_of_length_eq_zero h)
  have hQlen : Q.length = U.length + 2 := by simp [Q, Nat.add_assoc]
  obtain ⟨E, hE, hlen⟩ := exists_cycle_of_path_pair hP hQ hinter (by omega)
  exact ⟨E, hE, by omega⟩

/-- An outside path and a chosen simple arc supported on the cycle form
a cycle of the two path lengths plus the two attachment edges. -/
theorem exists_cycle_of_outside_path_and_cycle_arc {c A B x y : V}
    {C : G.Walk c c} {P : G.Walk A B} {U : G.Walk x y}
    (hP : P.IsPath) (hU : U.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hUC : ∀ v ∈ U.support, v ∈ C.support)
    (hAx : G.Adj A x) (hBy : G.Adj B y) :
    ∃ E : G.Walk A A, E.IsCycle ∧ E.length = P.length + U.length + 2 := by
  apply exists_cycle_of_disjoint_paths_and_attachments hP hU hAB
  · apply Set.disjoint_left.mpr
    intro v hvP hvU
    exact Set.disjoint_left.mp hPC hvP (hUC v hvU)
  · exact hAx
  · exact hBy

/-- The two complementary arcs between distinct attachment vertices each
close an outside path to a simple cycle, with the exact two-attachment
length formulas. -/
theorem exists_attachment_cycles_of_cycle_arcs {c A B x y : V}
    {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hx : x ∈ C.support) (hy : y ∈ C.support) (hxy : x ≠ y)
    (hAx : G.Adj A x) (hBy : G.Adj B y) :
    ∃ (U V' : G.Walk x y) (E F : G.Walk A A),
      U.IsPath ∧ V'.IsPath ∧
      (∀ v ∈ U.support, v ∈ C.support) ∧
      (∀ v ∈ V'.support, v ∈ C.support) ∧
      (∀ v ∈ U.support, v ∈ V'.support → v = x ∨ v = y) ∧
      U.length + V'.length = C.length ∧ E.IsCycle ∧ F.IsCycle ∧
      E.length = P.length + U.length + 2 ∧ F.length = P.length + V'.length + 2 := by
  obtain ⟨U, V', hU, hV, hUC, hVC, hinter, hlen⟩ := exists_cycle_arcs hC hx hy hxy
  obtain ⟨E, hE, hElen⟩ :=
    exists_cycle_of_outside_path_and_cycle_arc hP hU hAB hPC hUC hAx hBy
  obtain ⟨F, hF, hFlen⟩ :=
    exists_cycle_of_outside_path_and_cycle_arc hP hV hAB hPC hVC hAx hBy
  exact ⟨U, V', E, F, hU, hV, hUC, hVC, hinter, hlen, hE, hF, hElen, hFlen⟩

/-- A numeric form of the complementary attachment-cycle construction.
The two arc lengths are `t` and `C.length - t`; their two attachment
edges are counted separately in each resulting cycle. -/
theorem exists_complementary_attachment_cycle_lengths {c A B x y : V}
    {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hx : x ∈ C.support) (hy : y ∈ C.support) (hxy : x ≠ y)
    (hAx : G.Adj A x) (hBy : G.Adj B y) :
    ∃ (t : ℕ) (E F : G.Walk A A), 1 ≤ t ∧ t < C.length ∧ E.IsCycle ∧ F.IsCycle ∧
      E.length = P.length + t + 2 ∧ F.length = P.length + (C.length - t) + 2 := by
  obtain ⟨U, V', E, F, _, _, _, _, _, hsum, hE, hF, hElen, hFlen⟩ :=
    exists_attachment_cycles_of_cycle_arcs hC hP hAB hPC hx hy hxy hAx hBy
  have hUPos : 0 < U.length := Nat.pos_of_ne_zero fun h ↦ hxy (Walk.eq_of_length_eq_zero h)
  have hVPos : 0 < V'.length := Nat.pos_of_ne_zero fun h ↦ hxy (Walk.eq_of_length_eq_zero h)
  exact ⟨U.length, E, F, by omega, by omega, hE, hF, hElen, by omega⟩

/-- With the cycle based at the fixed neighbor of `B`, an attachment at
position `t` gives cycles using the arcs of lengths `t` and `N - t`. -/
theorem exists_attachment_cycles_at_index {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B} {t : ℕ}
    (hP : P.IsPath) (hAB : A ≠ B) (hC : C.IsCycle)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (htpos : 1 ≤ t) (htN : t < C.length)
    (hAtoT : G.Adj A (C.getVert t)) (hBtoBase : G.Adj B c) :
    ∃ E F : G.Walk A A, E.IsCycle ∧ F.IsCycle ∧
      E.length = P.length + t + 2 ∧ F.length = P.length + (C.length - t) + 2 := by
  have hUC : ∀ v ∈ (C.take t).reverse.support, v ∈ C.support := by
    intro v hv
    exact (C.isSubwalk_take t).support_subset (by simpa using hv)
  have hVC : ∀ v ∈ (C.drop t).support, v ∈ C.support := by
    intro v hv
    exact (C.isSubwalk_drop t).support_subset hv
  obtain ⟨E, hE, hElen⟩ := exists_cycle_of_outside_path_and_cycle_arc
    hP (hC.isPath_take htN).reverse hAB hPC hUC hAtoT hBtoBase
  obtain ⟨F, hF, hFlen⟩ := exists_cycle_of_outside_path_and_cycle_arc
    hP (hC.isPath_drop htpos) hAB hPC hVC hAtoT hBtoBase
  refine ⟨E, F, hE, hF, ?_, ?_⟩
  · simpa only [Walk.length_reverse, Walk.take_length, Nat.min_eq_left htN.le] using hElen
  · simpa only [Walk.drop_length] using hFlen

end JSP000078
