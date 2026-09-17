import JSP000078.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Basic properties of the set of distinct odd cycle lengths

These lemmas connect the finite set used by the main theorem with Mathlib
cycles and graph inclusions.
-/

namespace JSP000078

open SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W]
variable {G H : SimpleGraph V} {K : SimpleGraph W}

/-- Every recorded length is odd. -/
theorem odd_of_mem_oddCycleLengths {n : ℕ} (hn : n ∈ oddCycleLengths G) : Odd n :=
  (mem_oddCycleLengths G).mp hn |>.1

/-- Simple graphs have no cycles of length below three. -/
theorem three_le_of_mem_oddCycleLengths {n : ℕ} (hn : n ∈ oddCycleLengths G) : 3 ≤ n := by
  obtain ⟨_, v, p, hp, rfl⟩ := (mem_oddCycleLengths G).mp hn
  exact hp.three_le_length

/-- Every recorded cycle length is positive. -/
theorem pos_of_mem_oddCycleLengths {n : ℕ} (hn : n ∈ oddCycleLengths G) : 0 < n := by
  have := three_le_of_mem_oddCycleLengths hn
  omega

/-- Deleting edges cannot introduce a new odd cycle length. -/
theorem oddCycleLengths_mono (h : G ≤ H) : oddCycleLengths G ⊆ oddCycleLengths H := by
  intro n hn
  obtain ⟨ho, v, p, hp, hlen⟩ := (mem_oddCycleLengths G).mp hn
  apply (mem_oddCycleLengths H).mpr
  exact ⟨ho, v, p.mapLe h, hp.mapLe h, by simpa using hlen⟩

/-- Injective graph homomorphisms preserve all distinct odd cycle lengths. -/
theorem oddCycleLengths_subset_of_injective_hom (f : G →g K)
    (hf : Function.Injective f) : oddCycleLengths G ⊆ oddCycleLengths K := by
  intro n hn
  obtain ⟨ho, v, p, hp, hlen⟩ := (mem_oddCycleLengths G).mp hn
  apply (mem_oddCycleLengths K).mpr
  exact ⟨ho, f v, p.map f, hp.map hf, by simpa using hlen⟩

/-- Graph embeddings cannot introduce odd lengths in their domain. -/
theorem oddCycleLengths_subset_of_embedding (f : G ↪g K) :
    oddCycleLengths G ⊆ oddCycleLengths K :=
  oddCycleLengths_subset_of_injective_hom f.toHom f.injective

/-- Deleting vertices cannot introduce a new odd cycle length. -/
theorem oddCycleLengths_induce_subset (s : Set V) [Fintype s] :
    oddCycleLengths (G.induce s) ⊆ oddCycleLengths G :=
  oddCycleLengths_subset_of_embedding (SimpleGraph.Embedding.induce s)

/-- The set is empty exactly when the graph has no odd simple cycle. -/
theorem oddCycleLengths_eq_empty_iff : oddCycleLengths G = ∅ ↔
    ∀ (v : V) (p : G.Walk v v), p.IsCycle → ¬ Odd p.length := by
  constructor
  · intro h v p hp ho
    have hm : p.length ∈ oddCycleLengths G :=
      (mem_oddCycleLengths G).mpr ⟨ho, v, p, hp, rfl⟩
    simp [h] at hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨ho, v, p, hp, rfl⟩ := (mem_oddCycleLengths G).mp hn
    exact h v p hp ho

/-- Equivalently, emptiness says every simple cycle has even length. -/
theorem oddCycleLengths_eq_empty_iff_cycles_even : oddCycleLengths G = ∅ ↔
    ∀ (v : V) (p : G.Walk v v), p.IsCycle → Even p.length := by
  simp_rw [oddCycleLengths_eq_empty_iff, Nat.not_odd_iff_even]

/-- Every closed walk in a bipartite graph is even, so no odd cycle length occurs. -/
theorem oddCycleLengths_eq_empty_of_bipartite (h : G.IsBipartite) :
    oddCycleLengths G = ∅ := by
  apply oddCycleLengths_eq_empty_iff_cycles_even.mpr
  intro v p _
  exact (SimpleGraph.two_colorable_iff_forall_loop_even.mp h) v p

/-- Odd cycle lengths in a connected component also occur in the whole graph. -/
theorem oddCycleLengths_connectedComponent_subset (c : G.ConnectedComponent) [Fintype c] :
    oddCycleLengths c.toSimpleGraph ⊆ oddCycleLengths G :=
  oddCycleLengths_subset_of_injective_hom c.toSimpleGraph_hom Subtype.val_injective

/-- Edge deletion is a special case of monotonicity. -/
theorem oddCycleLengths_deleteEdges_subset (s : Set (Sym2 V)) :
    oddCycleLengths (G.deleteEdges s) ⊆ oddCycleLengths G :=
  oddCycleLengths_mono (G.deleteEdges_le s)

/-- The number of distinct odd cycle lengths decreases under edge deletion. -/
theorem card_oddCycleLengths_mono (h : G ≤ H) :
    (oddCycleLengths G).card ≤ (oddCycleLengths H).card :=
  Finset.card_le_card (oddCycleLengths_mono h)

end JSP000078
