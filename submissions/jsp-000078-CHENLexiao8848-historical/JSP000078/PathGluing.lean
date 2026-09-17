import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Gluing paths at prescribed intersections

These bridges express the support conditions in the form used for the two
links between disjoint cycles in Gyárfás's historical proof. The underlying
cycle construction reuses `SimpleGraph.Walk.IsPath.isCycle_append`.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The initial vertex occurs only at the beginning of a simple path. -/
theorem path_start_notMem_support_tail {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) : a ∉ p.support.tail := by
  have h : (a :: p.support.tail).Nodup := by
    simpa only [Walk.cons_tail_support] using hp.support_nodup
  exact (List.nodup_cons.mp h).1

/-- Two simple paths meeting only at their common endpoint concatenate to
a simple path. This includes paths of length zero. -/
theorem isPath_append_of_support_intersection {a v b : V}
    {p : G.Walk a v} {q : G.Walk v b} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x ∈ p.support, x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro x hxp hxq
  have hxv := hinter x hxp (List.mem_of_mem_tail hxq)
  subst x
  exact path_start_notMem_support_tail hq hxq

/-- Two simple paths directed around the same pair of endpoints form a
cycle if their only common vertices are those endpoints and the total
length is at least three. The lower bound excludes an edge followed by
its reversal. -/
theorem isCycle_append_of_support_intersection {a b : V}
    {p : G.Walk a b} {q : G.Walk b a} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b)
    (hlen : 3 ≤ p.length + q.length) : (p.append q).IsCycle := by
  apply hp.isCycle_append hq
  · rw [List.disjoint_left]
    intro x hxp hxq
    rcases hinter x (List.mem_of_mem_tail hxp) (List.mem_of_mem_tail hxq) with ha | hb
    · subst x
      exact path_start_notMem_support_tail hp hxp
    · subst x
      exact path_start_notMem_support_tail hq hxq
  · omega

/-- Two internally disjoint simple paths with the same endpoints form a
cycle when the second path is reversed, provided their total length is
at least three. -/
theorem isCycle_append_reverse_of_support_intersection {a b : V}
    {p q : G.Walk a b} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b)
    (hlen : 3 ≤ p.length + q.length) : (p.append q.reverse).IsCycle := by
  apply isCycle_append_of_support_intersection hp hq.reverse
  · intro x hxp hxq
    exact hinter x hxp (by simpa only [Walk.support_reverse, List.mem_reverse] using hxq)
  · simpa only [Walk.length_reverse] using hlen

/-- The cycle made from two internally disjoint paths has the sum of their
lengths. This packages the existing append/reverse length identities with
the support-based cycle criterion. -/
theorem exists_cycle_of_path_pair {a b : V} {p q : G.Walk a b}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b)
    (hlen : 3 ≤ p.length + q.length) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p.length + q.length := by
  exact ⟨p.append q.reverse,
    isCycle_append_reverse_of_support_intersection hp hq hinter hlen, by simp⟩

/-- Four simple paths around a ring form a cycle when neighboring paths
meet only at their shared endpoint and opposite paths have disjoint
supports. In the historical proof, two paths are arcs of the two original
cycles and the other two are the disjoint links between those cycles. -/
theorem isCycle_append_four_of_support_intersections {a b c d : V}
    {p : G.Walk a b} {q : G.Walk b c} {r : G.Walk c d} {s : G.Walk d a}
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (hs : s.IsPath)
    (hpq : ∀ x ∈ p.support, x ∈ q.support → x = b)
    (hqr : ∀ x ∈ q.support, x ∈ r.support → x = c)
    (hrs : ∀ x ∈ r.support, x ∈ s.support → x = d)
    (hsp : ∀ x ∈ s.support, x ∈ p.support → x = a)
    (hpr : Disjoint {x | x ∈ p.support} {x | x ∈ r.support})
    (hqs : Disjoint {x | x ∈ q.support} {x | x ∈ s.support})
    (hlen : 3 ≤ p.length + q.length + r.length + s.length) :
    ((p.append q).append (r.append s)).IsCycle := by
  apply isCycle_append_of_support_intersection
    (isPath_append_of_support_intersection hp hq hpq)
    (isPath_append_of_support_intersection hr hs hrs)
  · intro x hxpq hxrs
    rcases (Walk.mem_support_append_iff p q).mp hxpq with hxp | hxq
    · rcases (Walk.mem_support_append_iff r s).mp hxrs with hxr | hxs
      · exact (Set.disjoint_left.mp hpr hxp hxr).elim
      · exact Or.inl (hsp x hxs hxp)
    · rcases (Walk.mem_support_append_iff r s).mp hxrs with hxr | hxs
      · exact Or.inr (hqr x hxq hxr)
      · exact (Set.disjoint_left.mp hqs hxq hxs).elim
  · simpa only [Walk.length_append, Nat.add_assoc] using hlen

/-- If two walks concatenate to a cycle, their supports meet only at the
two endpoints. -/
theorem support_intersection_of_isCycle_append {a b : V}
    {p : G.Walk a b} {q : G.Walk b a} (hc : (p.append q).IsCycle) :
    ∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b := by
  have hd := hc.support_nodup
  rw [Walk.tail_support_append, List.nodup_append'] at hd
  intro x hxp hxq
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · exact Or.inr hxb
  exact (hd.2.2 ((p.mem_support_iff.mp hxp).resolve_left hxa)
    ((q.mem_support_iff.mp hxq).resolve_left hxb)).elim

end JSP000078
