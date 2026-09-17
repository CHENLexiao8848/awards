import JSP000078.HistoricalCountingSpec

/-!
# Alternating coloring of an even cycle with parity-preserving chords

Every vertex of the exact fan graph has a unique position before the repeated
endpoint of its spanning cycle. Coloring by that position modulo two respects
the rim edges, including the wrap-around edge, and every chord to an odd position.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

namespace CycleWithIncidentChords

/-- Every vertex of the spanning cycle has a position strictly before the
repeated final endpoint. -/
theorem exists_position (F : CycleWithIncidentChords H) (v : V) :
    ∃ i : ℕ, i < F.cycle.length ∧ F.cycle.getVert i = v := by
  obtain ⟨i, hi, hilen⟩ := Walk.mem_support_iff_exists_getVert.mp (F.spanning v)
  by_cases hlt : i < F.cycle.length
  · exact ⟨i, hlt, hi⟩
  · have heq : i = F.cycle.length := by omega
    refine ⟨0, by have := F.isCycle.three_le_length; omega, ?_⟩
    simpa only [heq, Walk.getVert_length, Walk.getVert_zero] using hi

/-- The unique nonterminal cycle position of a vertex. -/
noncomputable def position (F : CycleWithIncidentChords H) (v : V) : ℕ :=
  Classical.choose (F.exists_position v)

theorem position_lt (F : CycleWithIncidentChords H) (v : V) :
    F.position v < F.cycle.length :=
  (Classical.choose_spec (F.exists_position v)).1

theorem getVert_position (F : CycleWithIncidentChords H) (v : V) :
    F.cycle.getVert (F.position v) = v :=
  (Classical.choose_spec (F.exists_position v)).2

theorem position_getVert (F : CycleWithIncidentChords H) {i : ℕ}
    (hi : i < F.cycle.length) : F.position (F.cycle.getVert i) = i := by
  apply F.isCycle.getVert_injOn'
  · have := F.position_lt (F.cycle.getVert i)
    change F.position (F.cycle.getVert i) ≤ F.cycle.length - 1
    omega
  · change i ≤ F.cycle.length - 1
    omega
  · exact F.getVert_position (F.cycle.getVert i)

/-- An exact fan on an even base cycle is bipartite if every selected
proper chord joins the base to an odd cycle position. -/
theorem isBipartite_of_even_length_of_odd_indices (F : CycleWithIncidentChords H)
    (hlen : Even F.cycle.length) (hodd : ∀ j ∈ F.indices, Odd j.val) :
    H.IsBipartite := by
  let color : V → Fin 2 := fun v ↦ ⟨F.position v % 2, Nat.mod_lt _ (by decide)⟩
  have hlenPos : 0 < F.cycle.length := by
    have := F.isCycle.three_le_length
    omega
  have hbase : (color F.base).val = 0 := by
    have hp := F.position_getVert hlenPos
    simp only [Walk.getVert_zero] at hp
    change F.position F.base % 2 = 0
    rw [hp]
  have hcolor : ∀ i ≤ F.cycle.length,
      (color (F.cycle.getVert i)).val = i % 2 := by
    intro i hi
    by_cases hilt : i < F.cycle.length
    · exact congrArg (fun n ↦ n % 2) (F.position_getVert hilt)
    · have heq : i = F.cycle.length := by omega
      subst i
      rw [Walk.getVert_length, hbase]
      exact (Nat.even_iff.mp hlen).symm
  have hstep : ∀ i < F.cycle.length,
      color (F.cycle.getVert i) ≠ color (F.cycle.getVert (i + 1)) := by
    intro i hi heq
    have hval := congrArg Fin.val heq
    rw [hcolor i hi.le, hcolor (i + 1) (by omega)] at hval
    omega
  have hspoke : ∀ j ∈ F.indices, color F.base ≠ color (F.cycle.getVert j.val) := by
    intro j hj heq
    have hval := congrArg Fin.val heq
    rw [hbase, hcolor j.val j.isLt.le] at hval
    have hjodd := Nat.odd_iff.mp (hodd j hj)
    omega
  refine ⟨Coloring.mk color ?_⟩
  intro u v huv
  rcases (F.edge_exact u v).mp huv with hEdge | ⟨j, hj, heq⟩
  · obtain ⟨i, hi, heq⟩ := (F.cycle.mk_mem_edges_iff_exists).mp hEdge
    rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · simpa only [hu, hv] using hstep i hi
    · exact (by simpa only [hu, hv] using (hstep i hi).symm)
  · rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simpa only [hu, hv] using hspoke j hj
    · simpa only [hu, hv] using (hspoke j hj).symm

end CycleWithIncidentChords

end JSP000078
