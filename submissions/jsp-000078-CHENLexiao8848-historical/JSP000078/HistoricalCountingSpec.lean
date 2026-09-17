import JSP000078.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Exact counting targets from Gyárfás's Lemma 2

The proposition definitions below distinguish the direct odd-base argument
from the full incident-chord lemma, including its even-base case. They state
the remaining obligations without asserting them.
-/

namespace JSP000078

open SimpleGraph

/-- The odd-base part of Lemma 2 produces distinct odd cycle lengths strictly
below the length of the base cycle. Extra ambient edges do not affect this
lower bound. The indices exclude both cycle edges incident to the base. -/
def HistoricalOddBaseChordCounting : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (c : V) (C : G.Walk c c)
    (k : ℕ) (J : Finset (Fin C.length)),
    C.IsCycle → Odd C.length → 1 ≤ k → 2 * k - 1 ≤ J.card →
    (∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) →
    k ≤ ((oddCycleLengths G).filter fun n ↦ n < C.length).card

/-- An exact graph made from a simple cycle and a specified set of proper
chords at one vertex. The spanning and exact-edge clauses exclude unrelated
vertices and edges from the bipartiteness alternative in the source lemma. -/
structure CycleWithIncidentChords {V : Type*} (H : SimpleGraph V) where
  base : V
  cycle : H.Walk base base
  isCycle : cycle.IsCycle
  indices : Finset (Fin cycle.length)
  proper_indices : ∀ j ∈ indices, 2 ≤ j.val ∧ j.val + 2 ≤ cycle.length
  chord_adj : ∀ j ∈ indices, H.Adj base (cycle.getVert j.val)
  spanning : ∀ v : V, v ∈ cycle.support
  edge_exact : ∀ u v : V, H.Adj u v ↔
    s(u, v) ∈ cycle.edges ∨
      ∃ j ∈ indices, s(u, v) = s(base, cycle.getVert j.val)

/-- The remaining even-base counting obligation. Unlike the odd-base
statement, this does not claim that the odd lengths are shorter than the
base cycle. Nonbipartiteness concerns the exact cycle-and-chords graph. -/
def HistoricalEvenBaseChordCounting : Prop :=
  ∀ {V : Type} [Fintype V] (H : SimpleGraph V) (F : CycleWithIncidentChords H)
    (k : ℕ), 1 ≤ k → F.indices.card = 2 * k - 1 → Even F.cycle.length →
    ¬H.IsBipartite → k ≤ (oddCycleLengths H).card

/-- The complete statement of Gyárfás's Lemma 2 (printed page 43).
There are exactly `2 * k - 1` selected proper chords, all at the same vertex. -/
def HistoricalIncidentChordLemmaTwo : Prop :=
  ∀ {V : Type} [Fintype V] (H : SimpleGraph V) (F : CycleWithIncidentChords H)
    (k : ℕ), 1 ≤ k → F.indices.card = 2 * k - 1 →
    H.IsBipartite ∨ k ≤ (oddCycleLengths H).card

end JSP000078
