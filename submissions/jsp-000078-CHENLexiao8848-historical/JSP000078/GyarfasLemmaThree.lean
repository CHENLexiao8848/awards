import JSP000078.FanInternalPaths
import JSP000078.FanBaseCounting
import JSP000078.HistoricalPathLengthsSpec

/-!
# Gyárfás's bipartite fan path lemma

The base-endpoint case follows the two directions around the cycle. For
internal endpoints, three rectangles of spoke positions give the required
count, with the single-chord case handled by the complementary arc lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

/-- Reversal preserves path simplicity and distinctness of lengths. -/
theorem reverse_distinct_path_family {x y : V} {m : ℕ}
    (P : Fin m → H.Walk x y) (hP : ∀ i, (P i).IsPath)
    (hInj : Function.Injective fun i ↦ (P i).length) :
    ∃ Q : Fin m → H.Walk y x,
      (∀ i, (Q i).IsPath) ∧ Function.Injective (fun i ↦ (Q i).length) := by
  refine ⟨fun i ↦ (P i).reverse, fun i ↦ (hP i).reverse, ?_⟩
  intro i j hij
  apply hInj
  simpa only [Walk.length_reverse] using hij

/-- A cycle with 2k−1 incident chords supplies k+1 different path lengths
between every two distinct vertices. Bipartiteness is needed only for parity. -/
theorem CycleWithIncidentChords.exists_distinct_path_lengths
    (F : CycleWithIncidentChords H) (k : ℕ) (hk : 1 ≤ k)
    (hcard : F.indices.card = 2 * k - 1) (x y : V) (hxy : x ≠ y) :
    ∃ P : Fin (k + 1) → H.Walk x y,
      (∀ i, (P i).IsPath) ∧ Function.Injective (fun i ↦ (P i).length) := by
  have ordered : ∀ u v : V, u ≠ v → F.position u < F.position v →
      ∃ P : Fin (k + 1) → H.Walk u v,
        (∀ i, (P i).IsPath) ∧ Function.Injective (fun i ↦ (P i).length) := by
    intro u v huv huvpos
    by_cases hu : F.position u = 0
    · have hueq : F.base = u := by
        simpa [hu] using F.getVert_position u
      have hvpos : 1 ≤ F.position v := by omega
      obtain ⟨P, hP, hInj⟩ := F.exists_paths_from_base_position k hk hcard
        hvpos (F.position_lt v)
      let Q : Fin (k + 1) → H.Walk u v :=
        fun i ↦ (P i).copy hueq (F.getVert_position v)
      refine ⟨Q, ?_, ?_⟩
      · intro i
        simpa only [Q, Walk.isPath_copy] using hP i
      · intro i j hij
        apply hInj
        simpa only [Q, Walk.length_copy] using hij
    · have hup : 1 ≤ F.position u := by omega
      obtain ⟨P, hP, hInj⟩ := F.exists_paths_between_positions k hk hcard hup
        huvpos (F.position_lt v)
      let Q : Fin (k + 1) → H.Walk u v :=
        fun i ↦ (P i).copy (F.getVert_position u) (F.getVert_position v)
      refine ⟨Q, ?_, ?_⟩
      · intro i
        simpa only [Q, Walk.isPath_copy] using hP i
      · intro i j hij
        apply hInj
        simpa only [Q, Walk.length_copy] using hij
  have hposne : F.position x ≠ F.position y := by
    intro h
    apply hxy
    exact (F.getVert_position x).symm.trans ((congrArg F.cycle.getVert h).trans
      (F.getVert_position y))
  rcases lt_or_gt_of_ne hposne with hlt | hgt
  · exact ordered x y hxy hlt
  · obtain ⟨P, hP, hInj⟩ := ordered y x hxy.symm hgt
    exact reverse_distinct_path_family P hP hInj

/-- Gyárfás (1992), Lemma 3, printed page 44, including the required common parity. -/
theorem historicalBipartiteFanPathLengths : HistoricalBipartiteFanPathLengths := by
  intro V _ H F k hk hcard hB x y hxy
  obtain ⟨P, hP, hInj⟩ := F.exists_distinct_path_lengths k hk hcard x y hxy
  exact ⟨P, hP, hInj, fun i j ↦ walk_length_mod_two_eq_of_bipartite hB (P i) (P j)⟩

end JSP000078
