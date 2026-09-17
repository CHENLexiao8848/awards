import JSP000078.Main

/-!
# Sharpness of the odd-cycle-length coloring bound

A graph on at most `2 * k + 2` vertices has at most `k` distinct odd cycle
lengths. For the complete graph, the main theorem supplies the matching
lower bound, because all vertices require different colors.
-/

namespace JSP000078

open SimpleGraph

/-- At most `k` odd integers between three and the order of the graph can occur. -/
theorem card_oddCycleLengths_le_of_card_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hcard : Fintype.card V ≤ 2 * k + 2) :
    (oddCycleLengths G).card ≤ k := by
  have h : (oddCycleLengths G).card ≤ (Finset.range k).card := by
    apply Finset.card_le_card_of_injOn (fun n => (n - 3) / 2)
    · intro n hn
      apply Finset.mem_range.mpr
      change (n - 3) / 2 < k
      obtain ⟨ho, v, p, hp, hlen⟩ := (mem_oddCycleLengths G).mp hn
      have hbound := cycle_length_le_card G hp
      have hthree := hp.three_le_length
      obtain ⟨j, hj⟩ := ho
      omega
    · intro a ha b hb hab
      change (a - 3) / 2 = (b - 3) / 2 at hab
      have ha3 := three_le_of_mem_oddCycleLengths ha
      have hb3 := three_le_of_mem_oddCycleLengths hb
      obtain ⟨i, hi⟩ := odd_of_mem_oddCycleLengths ha
      obtain ⟨j, hj⟩ := odd_of_mem_oddCycleLengths hb
      omega
  simpa using h

/-- Every vertex of a complete graph needs a different color. -/
theorem chromaticNumber_complete_even (k : ℕ) :
    (⊤ : SimpleGraph (Fin (2 * k + 2))).chromaticNumber = (2 * k + 2 : ℕ) := by
  simp

/-- The complete graph on `2 * k + 2` vertices has exactly `k` distinct odd cycle lengths. -/
theorem card_oddCycleLengths_complete_even (k : ℕ) :
    (oddCycleLengths (⊤ : SimpleGraph (Fin (2 * k + 2)))).card = k := by
  apply Nat.le_antisymm
  · apply card_oddCycleLengths_le_of_card_le
    simp
  · have h := chromaticNumber_le_two_mul_oddCycleLengths_card_add_two
      (⊤ : SimpleGraph (Fin (2 * k + 2)))
    rw [chromaticNumber_complete_even] at h
    have hn : 2 * k + 2 ≤
        2 * (oddCycleLengths (⊤ : SimpleGraph (Fin (2 * k + 2)))).card + 2 := by
      exact_mod_cast h
    omega

/-- The published bound is attained for every nonnegative number of odd cycle lengths. -/
theorem oddCycleLengths_bound_sharp (k : ℕ) :
    ∃ G : SimpleGraph (Fin (2 * k + 2)),
      (oddCycleLengths G).card = k ∧ G.chromaticNumber = (2 * k + 2 : ℕ) :=
  ⟨⊤, card_oddCycleLengths_complete_even k, chromaticNumber_complete_even k⟩

end JSP000078
