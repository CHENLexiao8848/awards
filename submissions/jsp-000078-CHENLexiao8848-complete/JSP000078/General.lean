/-
Copyright 2026 The Formal Conjectures Authors (the final theorem statement).
The statement is used under Apache-2.0; see LICENSE-APACHE-2.0.
The new bridge proof is by the JSP-000078 formalization contributors, with
OpenAI Codex assistance, under the package MIT license.
-/
import JSP000078.FiniteEquality
import JSP000078.Compactness
import JSP000078.CycleLengths
import Mathlib.Data.Set.Card

/-!
# The full Erdős 58 statement for arbitrary graphs

The finite theorem follows from this project's historical structural route.
The extension uses the attributed fixed-palette compactness theorem twice.
See FULL_SCOPE_PROVENANCE.md for the source and contribution boundaries.
-/

namespace JSP000078

open SimpleGraph

/-- The finite representation records exactly the standard odd simple-cycle lengths. -/
theorem finite_oddCycleLengths_eq {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (oddCycleLengths G : Set ℕ) = G.oddCycleLengths := by
  ext n
  simp only [Finset.mem_coe, mem_oddCycleLengths, SimpleGraph.oddCycleLengths,
    SimpleGraph.cycleLengths, Set.mem_ofPred_eq]
  exact and_comm

/-- Every odd cycle in a finite induced graph is an odd cycle of the whole graph. -/
theorem induced_oddCycleLengths_subset {V : Type*} (G : SimpleGraph V) (s : Finset V) :
    (oddCycleLengths (G.induce (s : Set V)) : Set ℕ) ⊆ G.oddCycleLengths := by
  intro n hn
  obtain ⟨ho, v, p, hp, hlen⟩ := (mem_oddCycleLengths _).mp hn
  let e := SimpleGraph.Embedding.induce (G := G) (s : Set V)
  exact ⟨⟨e v, p.map e.toHom, hp.map e.injective, by simpa using hlen⟩, ho⟩

/-- The full upper bound, without any finiteness assumption on the vertices. -/
theorem colorable_of_finite_oddCycleLengths {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hfin : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k) :
    G.Colorable (2 * k + 2) := by
  classical
  apply colorable_of_finite_induced
  intro s
  apply colorable_of_card_oddCycleLengths_le
  have h := Set.ncard_le_ncard (induced_oddCycleLengths_subset G s) hfin
  simpa only [Set.ncard_coe_finset] using h.trans hk

/-- Absence of the extremal clique saves a color for arbitrary graphs. -/
theorem colorable_of_finite_oddCycleLengths_of_cliqueFree
    {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hfin : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k)
    (hfree : G.CliqueFree (2 * k + 2)) : G.Colorable (2 * k + 1) := by
  classical
  apply colorable_of_finite_induced
  intro s
  apply colorable_of_card_oddCycleLengths_le_of_cliqueFree
  · have h := Set.ncard_le_ncard (induced_oddCycleLengths_subset G s) hfin
    simpa only [Set.ncard_coe_finset] using h.trans hk
  · exact hfree.comap (SimpleGraph.Embedding.induce (s : Set V)).isContained

/-- The complete original statement: arbitrary vertex type, at most k odd
simple-cycle lengths, and both directions of the equality characterization. -/
theorem erdos_58 :
    ∀ {V : Type*} (G : SimpleGraph V) (k : ℕ),
      G.oddCycleLengths.Finite →
      G.oddCycleLengths.ncard ≤ k →
        G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
        (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
          (SimpleGraph.completeGraph (Fin (2 * k + 2))).IsContained G) := by
  intro V G k hfin hk
  have hupper := (colorable_of_finite_oddCycleLengths G k hfin hk).chromaticNumber_le
  have hcast : ((2 * k + 2 : ℕ) : ℕ∞) = (2 * k + 2 : ℕ∞) := by push_cast; rfl
  rw [hcast] at hupper
  refine ⟨hupper, ?_⟩
  constructor
  · intro heq
    by_contra hcopy
    have hfree : G.CliqueFree (2 * k + 2) := by
      by_contra hnot
      exact hcopy (SimpleGraph.topEmbeddingOfNotCliqueFree hnot).isContained
    have hsmall :=
      (colorable_of_finite_oddCycleLengths_of_cliqueFree G k hfin hk hfree).chromaticNumber_le
    rw [← hcast] at heq
    rw [heq] at hsmall
    have hn := ENat.natCast_le_natCast.mp hsmall
    omega
  · rintro ⟨f⟩
    apply le_antisymm hupper
    have hbound := SimpleGraph.chromaticNumber_mono_of_hom f.toHom
    simpa [SimpleGraph.completeGraph, SimpleGraph.chromaticNumber_top] using hbound

end JSP000078
