import JSP000078.PathSpokes
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Ring.Parity

/-!
# Routes along an outside path and its incident spokes

For every selected neighbor position `d` of the initial endpoint, traverse
that spoke and then the suffix of the path. The resulting lengths are
distinct, and their minimum is one more than the suffix after the last
selected neighbor. Pairing an earlier spoke with the last one gives the
short cycles used in Gyárfás's Lemma 4.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V}

/-- Lengths of the routes using one selected spoke and the remaining suffix. -/
def routeLengths (p : G.Walk a b) (S : Finset ℕ) : Finset ℕ :=
  S.image fun d ↦ p.length - d + 1

/-- Length of the suffix after the last selected spoke endpoint. -/
def routeTailLength (p : G.Walk a b) (S : Finset ℕ) (hS : S.Nonempty) : ℕ :=
  p.length - S.max' hS

theorem routeLengths_card (p : G.Walk a b) (S : Finset ℕ)
    (hbound : ∀ d ∈ S, d ≤ p.length) :
    (routeLengths p S).card = S.card := by
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  have hiL := hbound i hi
  have hjL := hbound j hj
  change p.length - i + 1 = p.length - j + 1 at hij
  omega

theorem routeTailLength_add_one_mem (p : G.Walk a b) (S : Finset ℕ)
    (hS : S.Nonempty) : routeTailLength p S hS + 1 ∈ routeLengths p S := by
  exact Finset.mem_image.mpr ⟨S.max' hS, S.max'_mem hS, rfl⟩

theorem routeTailLength_add_one_le_of_mem (p : G.Walk a b) (S : Finset ℕ)
    (hS : S.Nonempty) {u : ℕ} (hu : u ∈ routeLengths p S) :
    routeTailLength p S hS + 1 ≤ u := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
  have hdmax : d ≤ S.max' hS := S.le_max' d hd
  dsimp only [routeTailLength]
  omega

/-- Every route length is realized by a simple path on the original
path's vertex set, including the length-one route when the last vertex
itself is joined directly to the initial vertex. -/
theorem exists_path_of_mem_routeLengths {p : G.Walk a b}
    (hp : p.IsPath) (S : Finset ℕ)
    (hpositions : ∀ d ∈ S, 1 ≤ d ∧ d ≤ p.length)
    (hspokes : ∀ d ∈ S, G.Adj a (p.getVert d))
    {u : ℕ} (hu : u ∈ routeLengths p S) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = u ∧ q.support ⊆ p.support := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
  exact exists_path_of_path_start_spoke_support_subset hp
    (hpositions d hd).1 (hpositions d hd).2 (hspokes d hd)

/-- A route whose length differs evenly from the final suffix determines
the short cycle between its spoke and the last selected spoke. The parity
condition excludes the last spoke itself, whose difference is one. -/
theorem exists_cycle_of_even_mem_routeLengths {p : G.Walk a b}
    (hp : p.IsPath) (S : Finset ℕ) (hS : S.Nonempty)
    (hpositions : ∀ d ∈ S, 1 ≤ d ∧ d ≤ p.length)
    (hspokes : ∀ d ∈ S, G.Adj a (p.getVert d))
    {u : ℕ} (hu : u ∈ routeLengths p S)
    (heven : Even (u - routeTailLength p S hS)) :
    ∃ E : G.Walk a a, E.IsCycle ∧ E.length = u - routeTailLength p S hS + 1 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
  have hdmax : d ≤ S.max' hS := S.le_max' d hd
  have hdL := (hpositions d hd).2
  have hmaxL := (hpositions _ (S.max'_mem hS)).2
  have hmod := Nat.even_iff.mp heven
  dsimp only [routeTailLength] at hmod ⊢
  have hdlt : d < S.max' hS := by omega
  obtain ⟨E, hE, hlen⟩ := exists_cycle_of_path_start_two_spokes hp
    (hpositions d hd).1 hdlt hmaxL (hspokes d hd) (hspokes _ (S.max'_mem hS))
  exact ⟨E, hE, by omega⟩

end JSP000078
