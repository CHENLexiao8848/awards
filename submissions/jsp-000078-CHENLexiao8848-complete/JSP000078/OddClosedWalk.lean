import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.Nat.Find

/-!
# An odd closed walk contains an odd simple cycle

A shortest odd closed walk cannot contain a nonempty closed subwalk in
its tail: an odd one would itself be shorter, while deleting an even one
would leave a shorter odd closed walk. Its tail is therefore a path.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Every odd closed walk in a simple graph yields an odd simple cycle. -/
theorem exists_odd_cycle_of_odd_closedWalk {a : V} (p : G.Walk a a)
    (hpOdd : Odd p.length) :
    ∃ (v : V) (C : G.Walk v v), C.IsCycle ∧ Odd C.length := by
  classical
  let candidate : ℕ → Prop := fun n ↦ ∃ (v : V) (C : G.Walk v v), Odd C.length ∧ C.length = n
  have hex : ∃ n, candidate n := ⟨p.length, a, p, hpOdd, rfl⟩
  obtain ⟨v, C, hCOdd, hClen⟩ := Nat.find_spec hex
  have hminimal : ∀ (w : V) (q : G.Walk w w), Odd q.length → C.length ≤ q.length := by
    intro w q hq
    rw [hClen]
    exact Nat.find_min' hex ⟨w, q, hq, rfl⟩
  have hCNot : ¬C.Nil := by
    intro hnil
    have hzero : C.length = 0 := hnil.length_eq_zero
    simp only [hzero, Nat.not_odd_zero] at hCOdd
  have htailLen : C.tail.length + 1 = C.length := C.length_tail_add_one hCNot
  have htailPath : C.tail.IsPath := by
    rw [Walk.isPath_iff_isSubwalk_imp_nil]
    intro w q hqSub
    by_contra hqNot
    have hqpos : 0 < q.length := by
      exact (Walk.not_nil_iff_lt_length).mp hqNot
    have hqle : q.length ≤ C.tail.length := Walk.length_le_of_isSubwalk hqSub
    have hqEven : Even q.length := by
      apply Nat.not_odd_iff_even.mp
      intro hqOdd
      have hmin := hminimal w q hqOdd
      omega
    obtain ⟨r, s, hdecomp⟩ := hqSub
    let D : G.Walk v v := (r.append s).cons (C.adj_snd hCNot)
    have hDlen : D.length = r.length + s.length + 1 := by
      simp only [D, Walk.length_cons, Walk.length_append]
    have hClen' : C.length = r.length + q.length + s.length + 1 := by
      rw [hdecomp, Walk.length_append, Walk.length_append] at htailLen
      omega
    have hDOdd : Odd D.length := by
      have hCmod := Nat.odd_iff.mp hCOdd
      have hqmod := Nat.even_iff.mp hqEven
      rw [Nat.odd_iff]
      omega
    have hmin := hminimal v D hDOdd
    omega
  have hthree : 3 ≤ C.length := by
    have hCmod := Nat.odd_iff.mp hCOdd
    have hneOne : C.length ≠ 1 := by
      intro hOne
      have htailZero : C.tail.length = 0 := by omega
      have hsame : C.snd = v := Walk.eq_of_length_eq_zero htailZero
      have hAdj := C.adj_snd hCNot
      exact hAdj.ne hsame.symm
    omega
  exact ⟨v, C, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨htailPath, hthree⟩, hCOdd⟩

/-- If every simple cycle is even, every closed walk is even. -/
theorem closedWalk_even_of_cycles_even
    (hcycles : ∀ (v : V) (C : G.Walk v v), C.IsCycle → Even C.length)
    {a : V} (p : G.Walk a a) : Even p.length := by
  apply Nat.not_odd_iff_even.mp
  intro hpOdd
  obtain ⟨v, C, hC, hCOdd⟩ := exists_odd_cycle_of_odd_closedWalk p hpOdd
  exact (Nat.not_even_iff_odd.mpr hCOdd) (hcycles v C hC)

/-- Absence of odd simple cycles implies bipartiteness, without finiteness. -/
theorem isBipartite_of_no_odd_cycle
    (hcycles : ∀ (v : V) (C : G.Walk v v), C.IsCycle → ¬Odd C.length) :
    G.IsBipartite := by
  apply SimpleGraph.two_colorable_iff_forall_loop_even.mpr
  intro a p
  apply closedWalk_even_of_cycles_even (p := p)
  intro v C hC
  exact Nat.not_odd_iff_even.mp (hcycles v C hC)

/-- A simple graph is bipartite exactly when it has no odd simple cycle. -/
theorem isBipartite_iff_no_odd_cycle :
    G.IsBipartite ↔ ∀ (v : V) (C : G.Walk v v), C.IsCycle → ¬Odd C.length := by
  constructor
  · intro hG v C _ hOdd
    have hEven := (SimpleGraph.two_colorable_iff_forall_loop_even.mp hG) v C
    exact (Nat.not_even_iff_odd.mpr hOdd) hEven
  · exact isBipartite_of_no_odd_cycle

end JSP000078
