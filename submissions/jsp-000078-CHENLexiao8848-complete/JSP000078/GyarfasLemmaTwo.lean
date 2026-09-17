import JSP000078.OddCycleFan
import JSP000078.EvenCycleFan

/-! # Gyárfás's incident-chord counting lemma -/

namespace JSP000078

open SimpleGraph

/-- The exact odd-base counting obligation, with shorter-than-base witnesses. -/
theorem historicalOddBaseChordCounting : HistoricalOddBaseChordCounting := by
  intro V _ G c C k J hC hOdd hk hcard hJ
  exact odd_cycle_many_chords_shorter_lengths hC hOdd k hk J hcard hJ

/-- The exact nonbipartite even-base counting obligation. -/
theorem historicalEvenBaseChordCounting : HistoricalEvenBaseChordCounting := by
  intro V _ H F k hk hcard hEven hNon
  exact even_cycle_fan_many_odd_lengths F k hk hcard hEven hNon

/-- Universe-polymorphic form of Gyárfás's incident-chord lemma. -/
theorem incident_chord_bipartite_or_many_odd_lengths
    {V : Type*} [Fintype V] (H : SimpleGraph V) (F : CycleWithIncidentChords H)
    (k : ℕ) (hk : 1 ≤ k) (hcard : F.indices.card = 2 * k - 1) :
    H.IsBipartite ∨ k ≤ (oddCycleLengths H).card := by
  by_cases hb : H.IsBipartite
  · exact Or.inl hb
  apply Or.inr
  rcases Nat.even_or_odd F.cycle.length with hEven | hOdd
  · exact even_cycle_fan_many_odd_lengths F k hk hcard hEven hb
  · have hshort := odd_cycle_many_chords_shorter_lengths F.isCycle hOdd k hk
      F.indices hcard.ge (fun j hj ↦ ⟨(F.proper_indices j hj).1,
        (F.proper_indices j hj).2, F.chord_adj j hj⟩)
    exact hshort.trans (Finset.card_filter_le _ _)

/-- The exact source statement of Lemma 2. -/
theorem historicalIncidentChordLemmaTwo : HistoricalIncidentChordLemmaTwo := by
  intro V _ H F k hk hcard
  exact incident_chord_bipartite_or_many_odd_lengths H F k hk hcard

end JSP000078
