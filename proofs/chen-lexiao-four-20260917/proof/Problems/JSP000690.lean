import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# JSP-000690: a 3-colour-critical 3-uniform hypergraph of minimum degree 7

This file formalizes the *weak vertex-colouring* interpretation of the problem.
A proper colouring means that every hyperedge contains vertices of different
colours. It does not formalize the different transversal-critical interpretation.

The 22-edge example is from Ruiliang Li,
"On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7",
arXiv:2512.24850. Vertices numbered 1,...,9 there are numbered 0,...,8 here.
All finite certificates below are checked by Lean's kernel (`decide +kernel`);
no native decision oracle is used.
-/

namespace JSP000690

abbrev Vertex := Fin 9
abbrev Edge := Finset Vertex
abbrev EdgeFamily := Finset Edge

/-- Every edge has at least two different vertex colours. -/
def ProperColoring {k : ℕ} (E : EdgeFamily) (c : Vertex → Fin k) : Prop :=
  ∀ e ∈ E, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

instance {k : ℕ} (E : EdgeFamily) (c : Vertex → Fin k) :
    Decidable (ProperColoring E c) :=
  inferInstanceAs (Decidable (∀ e ∈ E, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v))

/-- Colours on vertices outside the vertex set are irrelevant for positive
numbers of colours. Only positive colourability is used for subgraphs below. -/
def Colorable (E : EdgeFamily) (k : ℕ) : Prop :=
  ∃ c : Vertex → Fin k, ProperColoring E c

/-- A finite simple hypergraph, with all edges contained in its vertex set. -/
structure FiniteHypergraph where
  vertices : Finset Vertex
  edges : EdgeFamily
  edge_subset_vertices : ∀ e ∈ edges, e ⊆ vertices

def IsSubgraph (K H : FiniteHypergraph) : Prop :=
  K.vertices ⊆ H.vertices ∧ K.edges ⊆ H.edges

def IsProperSubgraph (K H : FiniteHypergraph) : Prop :=
  IsSubgraph K H ∧ (K.vertices ≠ H.vertices ∨ K.edges ≠ H.edges)

def IsUniform (E : EdgeFamily) (r : ℕ) : Prop :=
  ∀ e ∈ E, e.card = r

def degree (E : EdgeFamily) (v : Vertex) : ℕ :=
  (E.filter (v ∈ ·)).card

/-- The chromatic number equals `k`, expressed without an arbitrary minimizer. -/
def HasChromaticNumber (E : EdgeFamily) (k : ℕ) : Prop :=
  Colorable E k ∧ ∀ j < k, ¬ Colorable E j

/-- The complete, duplicate-free list of the construction's hyperedges. -/
def edges : EdgeFamily :=
  ⟨↑([{0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5},
   {0, 3, 7}, {0, 3, 8}, {0, 4, 6}, {0, 4, 7},
   {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6},
   {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7},
   {2, 4, 7}, {2, 5, 6}, {3, 5, 7}, {3, 5, 8},
   {4, 6, 7}, {4, 6, 8}] : List Edge), by decide +kernel⟩

def exampleGraph : FiniteHypergraph where
  vertices := Finset.univ
  edges := edges
  edge_subset_vertices := by intro e he; exact Finset.subset_univ e

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem vertex_count : exampleGraph.vertices.card = 9 := by decide +kernel

theorem edge_count : edges.card = 22 := by decide +kernel

theorem three_uniform : IsUniform edges 3 := by
  unfold IsUniform
  decide +kernel

theorem degree_sequence :
    ∀ v : Vertex, degree edges v = if v = 0 then 10 else 7 := by
  decide +kernel

theorem minimum_degree_at_least_seven : ∀ v : Vertex, 7 ≤ degree edges v := by
  intro v
  rw [degree_sequence v]
  split <;> omega

theorem minimum_degree_is_seven :
    (∀ v : Vertex, 7 ≤ degree edges v) ∧ ∃ v : Vertex, degree edges v = 7 := by
  exact ⟨minimum_degree_at_least_seven, 1, by decide +kernel⟩

/-- The 512 vectors exhaust all possible assignments of two colours. -/
theorem binary_vectors_fail :
    ∀ a b c d e f g h i : Fin 2,
      ¬ ProperColoring edges ![a, b, c, d, e, f, g, h, i] := by
  decide +kernel

theorem coloring_as_vector (c : Vertex → Fin 2) :
    ![c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7, c 8] = c := by
  funext i
  fin_cases i <;> rfl

/-- Every possible two-colouring has a monochromatic hyperedge. -/
theorem not_two_colorable : ¬ Colorable edges 2 := by
  rintro ⟨c, hc⟩
  have h := binary_vectors_fail (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8)
  rw [coloring_as_vector] at h
  exact h hc

def threeColoring : Vertex → Fin 3 := ![0, 0, 1, 0, 0, 1, 2, 1, 1]

theorem three_colorable : Colorable edges 3 := by
  exact ⟨threeColoring, by decide +kernel⟩

/-- Explicit two-colouring certificate for each possible single-edge deletion. -/
def edgeDeletionColoring (e : Edge) : Vertex → Fin 2 :=
  if e = {0, 1, 2} then ![0, 0, 0, 0, 0, 1, 1, 1, 1] else
  if e = {0, 1, 8} then ![0, 0, 1, 1, 1, 0, 1, 0, 0] else
  if e = {0, 2, 7} then ![0, 1, 0, 1, 1, 0, 1, 0, 0] else
  if e = {0, 3, 5} then ![0, 0, 1, 0, 0, 0, 1, 1, 1] else
  if e = {0, 3, 7} then ![0, 0, 1, 0, 1, 1, 0, 0, 1] else
  if e = {0, 3, 8} then ![0, 1, 0, 0, 1, 1, 0, 1, 0] else
  if e = {0, 4, 6} then ![0, 0, 1, 0, 0, 1, 0, 1, 1] else
  if e = {0, 4, 7} then ![0, 0, 1, 1, 0, 0, 1, 0, 1] else
  if e = {0, 4, 8} then ![0, 1, 0, 1, 0, 0, 1, 1, 0] else
  if e = {0, 5, 6} then ![0, 1, 1, 1, 1, 0, 0, 0, 0] else
  if e = {1, 2, 5} then ![0, 1, 1, 1, 1, 1, 0, 0, 0] else
  if e = {1, 2, 6} then ![0, 1, 1, 1, 1, 0, 1, 0, 0] else
  if e = {1, 3, 8} then ![0, 1, 0, 1, 0, 0, 1, 1, 1] else
  if e = {1, 4, 8} then ![0, 1, 0, 0, 1, 1, 0, 1, 1] else
  if e = {1, 5, 6} then ![0, 1, 0, 0, 0, 1, 1, 1, 1] else
  if e = {2, 3, 7} then ![0, 0, 1, 1, 0, 0, 1, 1, 1] else
  if e = {2, 4, 7} then ![0, 0, 1, 0, 1, 1, 0, 1, 1] else
  if e = {2, 5, 6} then ![0, 0, 1, 0, 0, 1, 1, 1, 1] else
  if e = {3, 5, 7} then ![0, 1, 0, 1, 1, 1, 0, 1, 0] else
  if e = {3, 5, 8} then ![0, 0, 1, 1, 1, 1, 0, 0, 1] else
  if e = {4, 6, 7} then ![0, 1, 0, 1, 1, 0, 1, 1, 0] else
  ![0, 0, 1, 1, 1, 0, 1, 0, 1]

theorem edgeDeletionColoring_proper :
    ∀ e ∈ edges, ProperColoring (edges.erase e) (edgeDeletionColoring e) := by
  decide +kernel

/-- Every single edge is essential to non-two-colourability. -/
theorem erase_edge_two_colorable : ∀ e ∈ edges, Colorable (edges.erase e) 2 := by
  intro e he
  exact ⟨edgeDeletionColoring e, edgeDeletionColoring_proper e he⟩

/-- Removing edges preserves any proper colouring. -/
theorem colorable_of_subset {E F : EdgeFamily} {k : ℕ}
    (hEF : E ⊆ F) (hF : Colorable F k) : Colorable E k := by
  obtain ⟨c, hc⟩ := hF
  exact ⟨c, fun e he => hc e (hEF he)⟩

/-- Adding unused colours preserves colourability. -/
theorem colorable_mono {E : EdgeFamily} {j k : ℕ}
    (hjk : j ≤ k) (hE : Colorable E j) : Colorable E k := by
  obtain ⟨c, hc⟩ := hE
  refine ⟨fun v => Fin.castLE hjk (c v), ?_⟩
  intro e he
  obtain ⟨u, hu, v, hv, huv⟩ := hc e he
  exact ⟨u, hu, v, hv, fun h => huv (Fin.castLE_injective hjk h)⟩

theorem chromatic_number_three : HasChromaticNumber edges 3 := by
  refine ⟨three_colorable, ?_⟩
  intro j hj hcolor
  exact not_two_colorable (colorable_mono (by omega) hcolor)

/-- This general argument turns single-edge deletion into edge-criticality. -/
theorem every_strict_edge_subfamily_two_colorable {F : EdgeFamily}
    (hF : F ⊂ edges) : Colorable F 2 := by
  obtain ⟨e, he, hFe⟩ := Finset.ssubset_iff_exists_subset_erase.mp hF
  exact colorable_of_subset hFe (erase_edge_two_colorable e he)

theorem no_isolated_vertices : ∀ v : Vertex, ∃ e ∈ edges, v ∈ e := by
  intro v
  have hpos : 0 < (edges.filter (v ∈ ·)).card := by
    have h := minimum_degree_at_least_seven v
    unfold degree at h
    omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

/-- Deleting a vertex means discarding all hyperedges incident with that vertex. -/
theorem delete_vertex_two_colorable (v : Vertex) :
    Colorable (edges.filter fun e => v ∉ e) 2 := by
  obtain ⟨e, he, hv⟩ := no_isolated_vertices v
  apply colorable_of_subset (F := edges.erase e) ?_ (erase_edge_two_colorable e he)
  intro f hf
  obtain ⟨hfE, hvf⟩ := Finset.mem_filter.mp hf
  exact Finset.mem_erase.mpr ⟨fun hfe => hvf (hfe.symm ▸ hv), hfE⟩

/-- A hypergraph with an edge cannot be properly coloured with one colour. -/
theorem not_one_colorable_of_nonempty {E : EdgeFamily} (hE : E.Nonempty) :
    ¬ Colorable E 1 := by
  rintro ⟨c, hc⟩
  obtain ⟨e, he⟩ := hE
  obtain ⟨u, hu, v, hv, huv⟩ := hc e he
  exact huv (Subsingleton.elim _ _)

theorem chromatic_number_two_of_nonempty {E : EdgeFamily}
    (hE : E.Nonempty) (hcolor : Colorable E 2) : HasChromaticNumber E 2 := by
  refine ⟨hcolor, ?_⟩
  intro j hj hc
  exact not_one_colorable_of_nonempty hE (colorable_mono (by omega) hc)

theorem erase_edge_nonempty : ∀ e ∈ edges, (edges.erase e).Nonempty := by
  decide +kernel

theorem delete_vertex_nonempty :
    ∀ v : Vertex, (edges.filter fun e => v ∉ e).Nonempty := by
  decide +kernel

/-- Deleting one edge lowers the chromatic number to exactly two. -/
theorem erase_edge_chromatic_number_two (e : Edge) (he : e ∈ edges) :
    HasChromaticNumber (edges.erase e) 2 :=
  chromatic_number_two_of_nonempty (erase_edge_nonempty e he)
    (erase_edge_two_colorable e he)

/-- Deleting one vertex lowers the chromatic number to exactly two. -/
theorem delete_vertex_chromatic_number_two (v : Vertex) :
    HasChromaticNumber (edges.filter fun e => v ∉ e) 2 :=
  chromatic_number_two_of_nonempty (delete_vertex_nonempty v)
    (delete_vertex_two_colorable v)

/-- With no isolated vertices, even a vertex-only proper subgraph loses an edge. -/
theorem proper_subgraph_has_fewer_edges (K : FiniteHypergraph)
    (hK : IsProperSubgraph K exampleGraph) : K.edges ⊂ edges := by
  obtain ⟨⟨hKV, hKE⟩, hproper⟩ := hK
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hKE, ?_⟩
  intro hEq
  have hV : K.vertices = exampleGraph.vertices := by
    apply Finset.Subset.antisymm hKV
    intro v hv
    obtain ⟨e, he, hve⟩ := no_isolated_vertices v
    have heK : e ∈ K.edges := hEq.symm ▸ he
    exact K.edge_subset_vertices e heK hve
  rcases hproper with hproper | hproper
  · exact hproper hV
  · exact hproper hEq

/-- Arbitrary proper subgraphs, allowing vertices and/or edges to be removed,
have a two-colouring. This is the full weak-colour-critical property. -/
theorem every_proper_subgraph_two_colorable (K : FiniteHypergraph)
    (hK : IsProperSubgraph K exampleGraph) : Colorable K.edges 2 :=
  every_strict_edge_subfamily_two_colorable (proper_subgraph_has_fewer_edges K hK)

def IsThreeColorCritical (H : FiniteHypergraph) : Prop :=
  HasChromaticNumber H.edges 3 ∧
    ∀ K : FiniteHypergraph, IsProperSubgraph K H → Colorable K.edges 2

theorem example_is_three_color_critical : IsThreeColorCritical exampleGraph :=
  ⟨chromatic_number_three, every_proper_subgraph_two_colorable⟩

/-- JSP-000690, weak vertex-colouring version: there is a three-uniform
three-colour-critical hypergraph with nine vertices, 22 edges, and minimum
degree seven. In particular, a universal upper bound of six is false. -/
theorem solution :
    ∃ H : FiniteHypergraph,
      H.vertices.card = 9 ∧ H.edges.card = 22 ∧
      IsUniform H.edges 3 ∧ IsThreeColorCritical H ∧
      (∀ v ∈ H.vertices, 7 ≤ degree H.edges v) ∧
      (∃ v ∈ H.vertices, degree H.edges v = 7) := by
  refine ⟨exampleGraph, vertex_count, edge_count, three_uniform,
    example_is_three_color_critical, ?_, ?_⟩
  · exact fun v _ => minimum_degree_at_least_seven v
  · exact ⟨1, by decide +kernel, by decide +kernel⟩

end JSP000690
