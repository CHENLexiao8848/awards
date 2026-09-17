import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Paths from the base of a cycle through a spoke

An incident edge followed by an internal cycle segment gives a simple path
from the base to a prescribed cycle vertex. The exact lengths below form the
two endpoint-at-base path families in Gyárfás's Lemma 3.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Follow a spoke to position `i`, then the forward cycle segment to
position `t`. The segment may have length zero when `i = t`. -/
theorem exists_path_of_cycle_spoke_forward {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {i t : ℕ} (hi : 1 ≤ i) (hit : i ≤ t) (ht : t < C.length)
    (hai : G.Adj c (C.getVert i)) :
    ∃ p : G.Walk c (C.getVert t), p.IsPath ∧ p.length = t - i + 1 := by
  let R := (C.drop i).take (t - i)
  have hRlen : R.length = t - i := by
    simp only [R, Walk.take_length, Walk.drop_length]
    exact Nat.min_eq_left (by omega)
  have hend : (C.drop i).getVert (t - i) = C.getVert t := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le hit]
  let q : G.Walk (C.getVert i) (C.getVert t) := R.copy rfl hend
  have hqlen : q.length = t - i := by
    simpa only [q, Walk.length_copy] using hRlen
  have hq : q.IsPath := by
    simpa only [q, Walk.isPath_copy] using
      (hC.isPath_drop (by omega : 0 < i)).take (t - i)
  have hc : c ∉ q.support := by
    intro hcmem
    have hcR : c ∈ R.support := by
      simpa only [q, Walk.support_copy] using hcmem
    obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp hcR
    have hnle : n ≤ t - i := by omega
    have hget : C.getVert (i + n) = c := by
      simpa only [R, Walk.take_getVert, Nat.min_eq_right hnle, Walk.drop_getVert] using hn
    have hends := (hC.getVert_endpoint_iff (by omega : i + n ≤ C.length)).mp hget
    omega
  refine ⟨q.cons hai, (Walk.cons_isPath_iff hai q).mpr ⟨hq, hc⟩, ?_⟩
  simpa only [Walk.length_cons] using congrArg (fun n ↦ n + 1) hqlen

/-- Follow a spoke to position `i`, then the backward cycle segment to
position `t`. The segment may have length zero when `i = t`. -/
theorem exists_path_of_cycle_spoke_backward {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {i t : ℕ} (ht : 1 ≤ t) (hti : t ≤ i) (hi : i < C.length)
    (hai : G.Adj c (C.getVert i)) :
    ∃ p : G.Walk c (C.getVert t), p.IsPath ∧ p.length = i - t + 1 := by
  have hiRev : 1 ≤ C.length - i := by omega
  have horder : C.length - i ≤ C.length - t := by omega
  have htRev : C.length - t < C.reverse.length := by
    rw [Walk.length_reverse]
    omega
  have hadjRev : G.Adj c (C.reverse.getVert (C.length - i)) := by
    simpa only [Walk.getVert_reverse, Nat.sub_sub_self hi.le] using hai
  obtain ⟨q, hq, hqlen⟩ :=
    exists_path_of_cycle_spoke_forward hC.reverse hiRev horder htRev hadjRev
  have hend : C.reverse.getVert (C.length - t) = C.getVert t := by
    rw [Walk.getVert_reverse, Nat.sub_sub_self (by omega : t ≤ C.length)]
  refine ⟨q.copy rfl hend, ?_, ?_⟩
  · simpa only [Walk.isPath_copy] using hq
  · rw [Walk.length_copy, hqlen]
    omega

end JSP000078
