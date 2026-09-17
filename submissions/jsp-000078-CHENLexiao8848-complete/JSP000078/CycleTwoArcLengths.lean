import JSP000078.CycleSegments
import JSP000078.PathGluing

/-!
# Exact lengths of the two arcs between cycle positions

The forward nonwrapping segment has length equal to the difference of its
endpoint indices. The other arc follows the suffix through the base and then
the initial prefix; its length is the cycle length minus that difference.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Between ordered distinct cycle positions there are simple paths of the
two complementary arc lengths. The first position is allowed to be zero. -/
theorem exists_cycle_two_arcs_with_lengths {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {r s : ℕ} (hrs : r < s) (hs : s < C.length) :
    ∃ p q : G.Walk (C.getVert r) (C.getVert s),
      p.IsPath ∧ q.IsPath ∧ p.length = s - r ∧ q.length = C.length - (s - r) := by
  obtain ⟨p, hp, hplen, _⟩ := exists_cycle_segment hC hrs.le hs
  let tail := C.drop s
  let front := C.take r
  have htail : tail.IsPath := hC.isPath_drop (by omega)
  have hfront : front.IsPath := hC.isPath_take (by omega)
  have hinter : ∀ v ∈ tail.support, v ∈ front.support → v = c := by
    intro v hvt hvf
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hvt
    obtain ⟨m, hm, hml⟩ := Walk.mem_support_iff_exists_getVert.mp hvf
    have hnle : s + n ≤ C.length := by
      have hlen : tail.length = C.length - s := C.drop_length s
      omega
    have hmle : m ≤ r := by
      have hlen : front.length = r := by
        simp only [front, Walk.take_length, Nat.min_eq_left (by omega : r ≤ C.length)]
      omega
    have hnv : C.getVert (s + n) = v := by
      simpa only [tail, Walk.drop_getVert] using hn
    have hmv : C.getVert m = v := by
      simpa only [front, Walk.take_getVert, Nat.min_eq_right hmle] using hm
    by_cases hnend : s + n = C.length
    · have hcv : c = v := by simpa only [hnend, Walk.getVert_length] using hnv
      exact hcv.symm
    · have hindices : s + n = m := hC.getVert_injOn'
        (by change s + n ≤ C.length - 1; omega)
        (by change m ≤ C.length - 1; omega) (hnv.trans hmv.symm)
      omega
  have hcomp : (tail.append front).IsPath :=
    isPath_append_of_support_intersection htail hfront hinter
  refine ⟨p, (tail.append front).reverse, hp, hcomp.reverse, hplen, ?_⟩
  simp only [Walk.length_reverse, Walk.length_append, tail, front, Walk.drop_length,
    Walk.take_length, Nat.min_eq_left (by omega : r ≤ C.length)]
  omega

end JSP000078
