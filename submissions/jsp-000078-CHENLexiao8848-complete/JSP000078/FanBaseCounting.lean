import JSP000078.FanPositions
import JSP000078.FanBasePaths
import JSP000078.FanPathCounting
import JSP000078.PathParity
import JSP000078.EvenFanBipartite

/-! # The endpoint-at-base case of Gyárfás's Lemma 3 -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

/-- At least half the spoke positions produce different paths to a fixed
nonbase cycle vertex, using whichever direction contains more spokes. -/
theorem CycleWithIncidentChords.exists_paths_from_base_position
    (F : CycleWithIncidentChords H) (k : ℕ) (hk : 1 ≤ k)
    (hcard : F.indices.card = 2 * k - 1) {t : ℕ}
    (htpos : 1 ≤ t) (ht : t < F.cycle.length) :
    ∃ P : Fin (k + 1) → H.Walk F.base (F.cycle.getVert t),
      (∀ i, (P i).IsPath) ∧ Function.Injective (fun i ↦ (P i).length) := by
  classical
  let L := F.spokePositions.filter fun i ↦ i ≤ t
  let R := F.spokePositions.filter fun i ↦ ¬ i ≤ t
  have hsum : L.card + R.card = F.spokePositions.card :=
    F.spokePositions.card_filter_add_card_filter_not (fun i ↦ i ≤ t)
  have hsize := F.card_spokePositions
  by_cases hL : k + 1 ≤ L.card
  · let T := L.image fun i ↦ t - i + 1
    have hT : T.card = L.card := Finset.card_image_of_injOn (by
      intro i hi j hj heq
      have hiL : i ≤ t := (Finset.mem_filter.mp hi).2
      have hjL : j ≤ t := (Finset.mem_filter.mp hj).2
      change t - i + 1 = t - j + 1 at heq
      omega)
    have hreal : ∀ n ∈ T, ∃ p : H.Walk F.base (F.cycle.getVert t),
        p.IsPath ∧ p.length = n := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
      exact exists_path_of_cycle_spoke_forward F.isCycle
        (F.spokePosition_bounds his).1 hit ht (F.spokePosition_adj his)
    obtain ⟨P, hP, hInj, _⟩ :=
      exists_injective_length_paths_of_card_le T (k + 1) (by omega) hreal
    exact ⟨P, hP, hInj⟩
  · have hR : k + 1 ≤ R.card := by omega
    let T := R.image fun i ↦ i - t + 1
    have hT : T.card = R.card := Finset.card_image_of_injOn (by
      intro i hi j hj heq
      have hiR : ¬ i ≤ t := (Finset.mem_filter.mp hi).2
      have hjR : ¬ j ≤ t := (Finset.mem_filter.mp hj).2
      change i - t + 1 = j - t + 1 at heq
      omega)
    have hreal : ∀ n ∈ T, ∃ p : H.Walk F.base (F.cycle.getVert t),
        p.IsPath ∧ p.length = n := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
      exact exists_path_of_cycle_spoke_backward F.isCycle htpos (by omega)
        (F.spokePosition_bounds his).2 (F.spokePosition_adj his)
    obtain ⟨P, hP, hInj, _⟩ :=
      exists_injective_length_paths_of_card_le T (k + 1) (by omega) hreal
    exact ⟨P, hP, hInj⟩

/-- The published base-endpoint case, for an arbitrary vertex of the fan. -/
theorem CycleWithIncidentChords.exists_paths_from_base
    (F : CycleWithIncidentChords H) (k : ℕ) (hk : 1 ≤ k)
    (hcard : F.indices.card = 2 * k - 1) (hB : H.IsBipartite)
    (y : V) (hy : F.base ≠ y) :
    ∃ P : Fin (k + 1) → H.Walk F.base y,
      (∀ i, (P i).IsPath) ∧ Function.Injective (fun i ↦ (P i).length) ∧
      ∀ i j, (P i).length % 2 = (P j).length % 2 := by
  obtain ⟨t, ht, hty⟩ := F.exists_position y
  have htpos : 1 ≤ t := by
    by_contra h
    have hz : t = 0 := by omega
    exact hy (by simpa [hz] using hty)
  obtain ⟨P, hP, hInj⟩ := F.exists_paths_from_base_position k hk hcard htpos ht
  let Q : Fin (k + 1) → H.Walk F.base y := fun i ↦ (P i).copy rfl hty
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i
    simpa only [Q, Walk.isPath_copy] using hP i
  · intro i j heq
    apply hInj
    simpa only [Q, Walk.length_copy] using heq
  · intro i j
    exact walk_length_mod_two_eq_of_bipartite hB (Q i) (Q j)

end JSP000078
