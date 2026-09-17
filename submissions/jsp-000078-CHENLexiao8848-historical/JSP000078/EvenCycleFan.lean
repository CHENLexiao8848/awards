import JSP000078.FanPositions
import JSP000078.FanCounting
import JSP000078.TwoSpokeCycle
import JSP000078.EvenFanBipartite
import JSP000078.MathlibBridge

/-!
# Counting odd lengths in a nonbipartite even fan

The even-base part of Gyárfás's Lemma 2 is proved with an equivalent finite
count: cross-parity spoke positions give distinct odd absolute differences.
Adding two to a difference is the exact length of the two-spoke cycle.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {H : SimpleGraph V}

/-- Every odd distance between spokes supplies the corresponding odd cycle length. -/
theorem CycleWithIncidentChords.card_spoke_differences_le (F : CycleWithIncidentChords H) :
    (oddNatDifferences F.spokePositions).card ≤ (oddCycleLengths H).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun n : ℕ ↦ n + 2)
  · intro n hn
    obtain ⟨i, hi, j, hj, hij, hOdd, hlen⟩ :=
      (mem_oddNatDifferences_iff F.spokePositions n).mp hn
    obtain ⟨E, hE, hEL⟩ := exists_cycle_of_cycle_two_spokes F.isCycle
      (F.spokePosition_bounds hi).1 hij (F.spokePosition_bounds hj).2
      (F.spokePosition_adj hi) (F.spokePosition_adj hj)
    exact (mem_oddCycleLengths H).mpr
      ⟨(hlen ▸ hOdd).add_even even_two, F.base, E, hE, by
        change E.length = n + 2
        omega⟩
  · intro a _ b _ hab
    change a + 2 = b + 2 at hab
    omega

omit [Fintype V] in
/-- A nonbipartite fan on an even cycle has an even spoke position. -/
theorem CycleWithIncidentChords.even_spoke_nonempty (F : CycleWithIncidentChords H)
    (hEven : Even F.cycle.length) (hNon : ¬ H.IsBipartite) :
    (F.spokePositions.filter Even).Nonempty := by
  classical
  by_contra hEmpty
  apply hNon
  apply F.isBipartite_of_even_length_of_odd_indices hEven
  intro j hj
  apply Nat.not_even_iff_odd.mp
  intro hje
  apply hEmpty
  refine ⟨j.val, Finset.mem_filter.mpr ⟨?_, hje⟩⟩
  exact F.mem_spokePositions.mpr (Or.inr (Or.inr ⟨j, hj, rfl⟩))

/-- The even-base case of the incident-chord lemma. -/
theorem even_cycle_fan_many_odd_lengths (F : CycleWithIncidentChords H)
    (k : ℕ) (hk : 1 ≤ k) (hcard : F.indices.card = 2 * k - 1)
    (hEven : Even F.cycle.length) (hNon : ¬ H.IsBipartite) :
    k ≤ (oddCycleLengths H).card := by
  classical
  have hE := F.even_spoke_nonempty hEven hNon
  have hO : (F.spokePositions.filter Odd).Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨F.mem_spokePositions.mpr (Or.inl rfl), odd_one⟩⟩
  have hsize : 2 * k + 1 ≤ F.spokePositions.card := by
    rw [F.card_spokePositions, hcard]
    omega
  exact (le_card_oddNatDifferences F.spokePositions hE hO k hsize).trans
    F.card_spoke_differences_le

end JSP000078
