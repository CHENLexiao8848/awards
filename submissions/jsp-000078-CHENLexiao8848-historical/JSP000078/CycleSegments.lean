import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Internal segments of a simple cycle

Segments with indices strictly before the repeated terminal vertex are simple
paths, and their supports are exactly the vertices in the corresponding closed
index interval. Separated index intervals therefore have disjoint supports.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The segment of a simple cycle on the closed index interval `[i,j]`.
Both zero as the initial index and a segment of length zero are allowed. -/
theorem exists_cycle_segment {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    {i j : ℕ} (hij : i ≤ j) (hj : j < C.length) :
    ∃ q : G.Walk (C.getVert i) (C.getVert j),
      q.IsPath ∧ q.length = j - i ∧
      (∀ v : V, v ∈ q.support ↔ ∃ n : ℕ, i ≤ n ∧ n ≤ j ∧ C.getVert n = v) := by
  let R := (C.take j).drop i
  have hstart : (C.take j).getVert i = C.getVert i := by
    rw [Walk.take_getVert, Nat.min_eq_right hij]
  let q : G.Walk (C.getVert i) (C.getVert j) := R.copy hstart rfl
  have hRlen : R.length = j - i := by
    simp only [R, Walk.drop_length, Walk.take_length, Nat.min_eq_left hj.le]
  have hqlen : q.length = j - i := by
    simpa only [q, Walk.length_copy] using hRlen
  refine ⟨q, ?_, hqlen, ?_⟩
  · simpa only [q, Walk.isPath_copy] using (hC.isPath_take hj).drop i
  · intro v
    constructor
    · intro hv
      have hvR : v ∈ R.support := by
        simpa only [q, Walk.support_copy] using hv
      obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp hvR
      have hnle : i + n ≤ j := by omega
      refine ⟨i + n, by omega, hnle, ?_⟩
      simpa only [R, Walk.drop_getVert, Walk.take_getVert, Nat.min_eq_right hnle] using hn
    · rintro ⟨n, hin, hnj, hnv⟩
      have hget : R.getVert (n - i) = v := by
        simpa only [R, Walk.drop_getVert, Nat.add_sub_of_le hin, Walk.take_getVert,
          Nat.min_eq_right hnj] using hnv
      have hvR : v ∈ R.support := Walk.mem_support_iff_exists_getVert.mpr
        ⟨n - i, hget, by omega⟩
      simpa only [q, Walk.support_copy] using hvR

/-- Support contained in separated nonwrapping cycle intervals is disjoint.
The walks need not themselves be paths; the interval containments suffice. -/
theorem disjoint_support_of_separated_cycle_intervals
    {c a b d e : V} {C : G.Walk c c} (hC : C.IsCycle)
    {p : G.Walk a b} {q : G.Walk d e} {i j r s : ℕ}
    (hsep : j < r) (hs : s < C.length)
    (hp : ∀ v ∈ p.support, ∃ n : ℕ, i ≤ n ∧ n ≤ j ∧ C.getVert n = v)
    (hq : ∀ v ∈ q.support, ∃ n : ℕ, r ≤ n ∧ n ≤ s ∧ C.getVert n = v) :
    Disjoint {v : V | v ∈ p.support} {v : V | v ∈ q.support} := by
  apply Set.disjoint_left.mpr
  intro v hvp hvq
  obtain ⟨n, _, hnj, hnv⟩ := hp v hvp
  obtain ⟨m, hrm, hms, hmv⟩ := hq v hvq
  have hnm : n = m := hC.getVert_injOn'
    (by change n ≤ C.length - 1; omega)
    (by change m ≤ C.length - 1; omega) (hnv.trans hmv.symm)
  omega

end JSP000078
