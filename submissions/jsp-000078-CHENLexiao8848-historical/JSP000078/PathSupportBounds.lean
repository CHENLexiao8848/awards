import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Endpoint neighbors of a longest path

A neighbor outside the support could be prefixed or appended to a simple path.
Consequently, endpoints of a path longest in a prescribed vertex set have no
neighbors elsewhere in that set. These are the endpoint facts used for a
longest path in the complement of the chosen odd cycle.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b v : V}

/-- Every neighbor of the initial endpoint of a globally longest simple path
already lies on that path. No finiteness assumption is needed for this implication. -/
theorem neighbor_mem_support_of_longest_path_start
    {p : G.Walk a b} (hp : p.IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    (hav : G.Adj a v) : v ∈ p.support := by
  by_contra hv
  have hnew : (p.cons hav.symm).IsPath := hp.cons hv
  have hlen := hmax v b (p.cons hav.symm) hnew
  simp only [Walk.length_cons] at hlen
  omega

/-- The analogous endpoint containment at the final vertex of a longest path. -/
theorem neighbor_mem_support_of_longest_path_end
    {p : G.Walk a b} (hp : p.IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    (hbv : G.Adj b v) : v ∈ p.support := by
  have hrev : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.reverse.length := by
    intro x y q hq
    simpa only [Walk.length_reverse] using hmax x y q hq
  have hv := neighbor_mem_support_of_longest_path_start hp.reverse hrev hbv
  simpa only [Walk.support_reverse, List.mem_reverse] using hv

/-- If a path is longest among paths supported in `S`, each initial-endpoint
neighbor in `S` is on the path. -/
theorem neighbor_mem_support_of_longest_path_start_in_set
    {S : Set V} {p : G.Walk a b} (hp : p.IsPath)
    (hsub : ∀ w ∈ p.support, w ∈ S)
    (hmax : ∀ (x y : V) (q : G.Walk x y),
      q.IsPath → (∀ w ∈ q.support, w ∈ S) → q.length ≤ p.length)
    (hav : G.Adj a v) (hvS : v ∈ S) : v ∈ p.support := by
  by_contra hv
  have hnew : (p.cons hav.symm).IsPath := hp.cons hv
  have hnewS : ∀ w ∈ (p.cons hav.symm).support, w ∈ S := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hwp
    · exact hvS
    · exact hsub w hwp
  have hlen := hmax v b (p.cons hav.symm) hnew hnewS
  simp only [Walk.length_cons] at hlen
  omega

/-- The restricted longest-path neighbor containment at the final endpoint. -/
theorem neighbor_mem_support_of_longest_path_end_in_set
    {S : Set V} {p : G.Walk a b} (hp : p.IsPath)
    (hsub : ∀ w ∈ p.support, w ∈ S)
    (hmax : ∀ (x y : V) (q : G.Walk x y),
      q.IsPath → (∀ w ∈ q.support, w ∈ S) → q.length ≤ p.length)
    (hbv : G.Adj b v) (hvS : v ∈ S) : v ∈ p.support := by
  have hsubRev : ∀ w ∈ p.reverse.support, w ∈ S := by
    intro w hw
    exact hsub w (by simpa only [Walk.support_reverse, List.mem_reverse] using hw)
  have hmaxRev : ∀ (x y : V) (q : G.Walk x y),
      q.IsPath → (∀ w ∈ q.support, w ∈ S) → q.length ≤ p.reverse.length := by
    intro x y q hq hqS
    simpa only [Walk.length_reverse] using hmax x y q hq hqS
  have hv := neighbor_mem_support_of_longest_path_start_in_set hp.reverse hsubRev hmaxRev hbv hvS
  simpa only [Walk.support_reverse, List.mem_reverse] using hv

/-- Outside a forbidden vertex set, a longest path's initial endpoint has
neighbors only in that forbidden set or on the path itself. -/
theorem neighbor_mem_forbidden_or_support_of_longest_path_start
    {S : Set V} {p : G.Walk a b} (hp : p.IsPath)
    (havoid : ∀ w ∈ p.support, w ∉ S)
    (hmax : ∀ (x y : V) (q : G.Walk x y),
      q.IsPath → (∀ w ∈ q.support, w ∉ S) → q.length ≤ p.length)
    (hav : G.Adj a v) : v ∈ S ∨ v ∈ p.support := by
  by_cases hvS : v ∈ S
  · exact Or.inl hvS
  · exact Or.inr (neighbor_mem_support_of_longest_path_start_in_set
      (S := Sᶜ) hp havoid hmax hav hvS)

/-- The forbidden-set alternative at the final endpoint. -/
theorem neighbor_mem_forbidden_or_support_of_longest_path_end
    {S : Set V} {p : G.Walk a b} (hp : p.IsPath)
    (havoid : ∀ w ∈ p.support, w ∉ S)
    (hmax : ∀ (x y : V) (q : G.Walk x y),
      q.IsPath → (∀ w ∈ q.support, w ∉ S) → q.length ≤ p.length)
    (hbv : G.Adj b v) : v ∈ S ∨ v ∈ p.support := by
  by_cases hvS : v ∈ S
  · exact Or.inl hvS
  · exact Or.inr (neighbor_mem_support_of_longest_path_end_in_set
      (S := Sᶜ) hp havoid hmax hbv hvS)

end JSP000078
