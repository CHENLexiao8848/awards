import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sort

/-!
# Selecting fixed-endpoint paths of distinct lengths

A finite set of realized path lengths gives a path family indexed by `Fin m`
whenever its cardinality is at least `m`. This isolates the choice of paths
from the arithmetic estimates for the length set in Gyárfás's Lemma 3.
-/

namespace JSP000078

open SimpleGraph

/-- Select paths in increasing order of length from any sufficiently large
finite set of lengths realized between the same two endpoints. -/
theorem exists_strictMono_length_paths_of_card_le
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (S : Finset ℕ) (m : ℕ) (hm : m ≤ S.card)
    (hS : ∀ n ∈ S, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n) :
    ∃ P : Fin m → G.Walk x y,
      (∀ i, (P i).IsPath) ∧
      StrictMono (fun i ↦ (P i).length) ∧
      (∀ i, (P i).length ∈ S) := by
  classical
  let e : Fin m ↪o ℕ := S.orderEmbOfCardLe hm
  have he (i : Fin m) : e i ∈ S := S.orderEmbOfCardLe_mem hm i
  choose P hP hlen using fun i : Fin m ↦ hS (e i) (he i)
  refine ⟨P, hP, ?_, ?_⟩
  · intro i j hij
    simpa only [hlen] using e.strictMono hij
  · intro i
    rw [hlen]
    exact he i

/-- Cardinality bounds on a finite set of realized lengths give a family
of paths whose lengths are pairwise different. -/
theorem exists_injective_length_paths_of_card_le
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (S : Finset ℕ) (m : ℕ) (hm : m ≤ S.card)
    (hS : ∀ n ∈ S, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n) :
    ∃ P : Fin m → G.Walk x y,
      (∀ i, (P i).IsPath) ∧
      Function.Injective (fun i ↦ (P i).length) ∧
      (∀ i, (P i).length ∈ S) := by
  obtain ⟨P, hP, hmono, hmem⟩ :=
    exists_strictMono_length_paths_of_card_le S m hm hS
  exact ⟨P, hP, hmono.injective, hmem⟩

end JSP000078
