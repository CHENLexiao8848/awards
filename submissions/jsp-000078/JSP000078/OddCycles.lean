import JSP000078.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Cycles obtained from chords of a simple path

Closing an initial segment of a simple path by an edge from its initial
vertex gives a cycle. This records the exact length needed to distinguish
odd cycles arising from different positions in a depth-first stack.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A chord from the start of a simple path to its vertex at position `j`
produces a cycle with `j + 1` edges when `j ≥ 2`. -/
theorem exists_cycle_of_path_getVert_adj {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) {j : ℕ} (hj : j ≤ p.length) (hj2 : 2 ≤ j)
    (ha : G.Adj x (p.getVert j)) :
    ∃ c : G.Walk x x, c.IsCycle ∧ c.length = j + 1 := by
  let c : G.Walk x x := .cons ha (p.take j).reverse
  have hlen : c.length = j + 1 := by
    simp [c, Nat.min_eq_left hj]
  refine ⟨c, ?_, hlen⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · simpa [c] using (hp.take j).reverse
  · omega

/-- The list form of `exists_cycle_of_path_getVert_adj`, suitable for a
DFS stack whose head is the newly visited vertex. -/
theorem exists_cycle_of_chain_getElem_adj (x : V) (l : List V)
    (hnd : (x :: l).Nodup) (hc : (x :: l).IsChain G.Adj)
    (j : ℕ) (hj : j < (x :: l).length) (hj2 : 2 ≤ j)
    (ha : G.Adj x ((x :: l)[j])) :
    ∃ c : G.Walk x x, c.IsCycle ∧ c.length = j + 1 := by
  let p := Walk.ofSupport (x :: l) (List.cons_ne_nil x l) hc
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    simpa only [p, Walk.support_ofSupport] using hnd
  have hplen : p.length = l.length := by
    simpa only [p, List.length_cons, Nat.add_sub_cancel] using
      (Walk.length_ofSupport (List.cons_ne_nil x l) hc)
  have hjp : j ≤ p.length := by
    simp only [List.length_cons] at hj
    omega
  have hget : p.getVert j = (x :: l)[j] := by
    rw [p.getVert_eq_support_getElem hjp]
    simp only [p, Walk.support_ofSupport]
  exact exists_cycle_of_path_getVert_adj hp hjp hj2 (hget.symm ▸ ha)

/-- With the new vertex separate from the existing stack, stack position
`i ≥ 1` gives a cycle of length `i + 2`. -/
theorem exists_cycle_of_stack_getElem_adj (x : V) (l : List V)
    (hnd : (x :: l).Nodup) (hc : (x :: l).IsChain G.Adj)
    (i : ℕ) (hi : i < l.length) (hi1 : 1 ≤ i)
    (ha : G.Adj x (l[i])) :
    ∃ c : G.Walk x x, c.IsCycle ∧ c.length = i + 2 := by
  have hj : i + 1 < (x :: l).length := by simpa using hi
  have hj2 : 2 ≤ i + 1 := by omega
  have ha' : G.Adj x ((x :: l)[i + 1]) := by simpa using ha
  simpa [Nat.add_assoc] using
    exists_cycle_of_chain_getElem_adj x l hnd hc (i + 1) hj hj2 ha'

/-- Positions in the existing stack that are odd and adjacent to the new
vertex. Such positions yield distinct odd cycle lengths. -/
noncomputable def oddStackNeighborIndices (G : SimpleGraph V) (x : V) (l : List V) :
    Finset (Fin l.length) := by
  classical
  exact Finset.univ.filter fun i => Odd i.val ∧ G.Adj x (l[i.val])

@[simp]
theorem mem_oddStackNeighborIndices (x : V) (l : List V) (i : Fin l.length) :
    i ∈ oddStackNeighborIndices G x l ↔ Odd i.val ∧ G.Adj x (l[i.val]) := by
  classical
  simp [oddStackNeighborIndices]

/-- Each odd stack-neighbor position supplies a different odd cycle length. -/
theorem card_oddStackNeighborIndices_le [Fintype V] (x : V) (l : List V)
    (hnd : (x :: l).Nodup) (hc : (x :: l).IsChain G.Adj) :
    (oddStackNeighborIndices G x l).card ≤ (oddCycleLengths G).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun i : Fin l.length => i.val + 2)
  · intro i hi
    obtain ⟨hiodd, hiadj⟩ := (mem_oddStackNeighborIndices x l i).mp hi
    have hipos : 1 ≤ i.val := by
      have := Nat.odd_iff.mp hiodd
      omega
    obtain ⟨c, hcycle, hlength⟩ :=
      exists_cycle_of_stack_getElem_adj x l hnd hc i.val i.isLt hipos hiadj
    apply (mem_oddCycleLengths G).mpr
    exact ⟨hiodd.add_even even_two, x, c, hcycle, hlength⟩
  · intro i hi j hj hij
    apply Fin.ext
    change i.val + 2 = j.val + 2 at hij
    omega

end JSP000078
