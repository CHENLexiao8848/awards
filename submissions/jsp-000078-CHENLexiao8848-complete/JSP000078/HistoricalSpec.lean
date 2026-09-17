import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Definitions for the historical proof route

The numerical theorem in Main follows the verified historical structural proof.
This file defines the structural linking statement used by Gyárfás's published
proof. HistoricalLinking proves it by an elementary shortest-stem argument.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V]

/-- Finite vertex 2-connectivity, expressed through deletion of one vertex. -/
def TwoVertexConnected (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧
    ∀ z : V, (G.induce ({z} : Set V)ᶜ).Connected

/-- The precise two-link conclusion needed in Gyárfás's Lemma 1.
This is a proposition definition, with no assertion that it holds. -/
def TwoDisjointCycleLinks (G : SimpleGraph V) : Prop :=
  ∀ (c d : V) (C : G.Walk c c) (D : G.Walk d d),
    C.IsCycle → D.IsCycle →
    Disjoint {v : V | v ∈ C.support} {v : V | v ∈ D.support} →
    ∃ (a₁ a₂ b₁ b₂ : V) (P₁ : G.Walk a₁ b₁) (P₂ : G.Walk a₂ b₂),
      P₁.IsPath ∧ P₂.IsPath ∧
      a₁ ∈ C.support ∧ a₂ ∈ C.support ∧
      b₁ ∈ D.support ∧ b₂ ∈ D.support ∧
      Disjoint {v : V | v ∈ P₁.support} {v : V | v ∈ P₂.support} ∧
      (∀ v ∈ P₁.support, v ∈ C.support → v = a₁) ∧
      (∀ v ∈ P₂.support, v ∈ C.support → v = a₂) ∧
      (∀ v ∈ P₁.support, v ∈ D.support → v = b₁) ∧
      (∀ v ∈ P₂.support, v ∈ D.support → v = b₂)

/-- The published-proof linking statement; proved in HistoricalLinking. -/
def HistoricalCycleLinking : Prop :=
  ∀ {W : Type} [Fintype W] (G : SimpleGraph W),
    TwoVertexConnected G → TwoDisjointCycleLinks G

/-- Ordinary connectivity after deletion supplies one simple path avoiding
the deleted vertex. This helper does not assume the simultaneous two-link result. -/
theorem exists_path_in_vertex_deletion
    {G : SimpleGraph V} (hG : TwoVertexConnected G) (z : V)
    (a b : ↑(({z} : Set V)ᶜ)) :
    ∃ p : (G.induce ({z} : Set V)ᶜ).Walk a b, p.IsPath :=
  (hG.2.2 z).exists_isPath a b

end JSP000078
