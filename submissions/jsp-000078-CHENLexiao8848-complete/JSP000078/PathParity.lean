import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! # Fixed-endpoint walk parity in bipartite graphs -/

namespace JSP000078

open SimpleGraph

/-- Two walks with the same endpoints in a bipartite graph have the same parity. -/
theorem walk_length_mod_two_eq_of_bipartite {V : Type*} {G : SimpleGraph V}
    (hG : G.IsBipartite) {a b : V} (p q : G.Walk a b) :
    p.length % 2 = q.length % 2 := by
  have he := (SimpleGraph.two_colorable_iff_forall_loop_even.mp hG) a (p.append q.reverse)
  simp only [Walk.length_append, Walk.length_reverse, Nat.even_iff] at he
  omega

end JSP000078
