import JSP000078.GyarfasStructural
import JSP000078.HistoricalColoring
import JSP000078.FiniteGraphTransport

/-!
# JSP-000078: chromatic number and distinct odd cycle lengths

The sharp Bollobás–Erdős bound, established by Gyárfás (1992):
a finite simple graph with at most `k` odd cycle lengths is `(2k + 2)`-colorable.

The proof discharges the historical structural theorem, derives its coloring
consequence by vertex-count induction, and transports finite models across
vertex universes. No structural or coloring conclusion is left as a premise.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- A finite graph with at most `k` distinct odd cycle lengths has a proper
coloring with `2 * k + 2` colors. -/
theorem colorable_of_card_oddCycleLengths_le (k : ℕ)
    (hk : (oddCycleLengths G).card ≤ k) : G.Colorable (2 * k + 2) := by
  apply colorable_of_fin_models_of_card_le ?_ G k hk
  intro n H
  exact colorable_of_structural_theorem historicalGyarfasStructuralTheorem
    H (oddCycleLengths H).card le_rfl

/-- The sharp coloring bound in terms of the number of distinct odd cycle lengths. -/
theorem colorable_two_mul_oddCycleLengths_card_add_two :
    G.Colorable (2 * (oddCycleLengths G).card + 2) :=
  colorable_of_card_oddCycleLengths_le G _ le_rfl

/-- JSP-000078 in Mathlib's chromatic-number notation. -/
theorem chromaticNumber_le_two_mul_oddCycleLengths_card_add_two :
    G.chromaticNumber ≤ (2 * (oddCycleLengths G).card + 2 : ℕ) :=
  (colorable_two_mul_oddCycleLengths_card_add_two G).chromaticNumber_le

/-- The equivalent at-most-`k` version of the chromatic-number bound. -/
theorem chromaticNumber_le_of_card_oddCycleLengths_le (k : ℕ)
    (hk : (oddCycleLengths G).card ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ) :=
  (colorable_of_card_oddCycleLengths_le G k hk).chromaticNumber_le

/-- The original exact-`k` formulation: `k` counts distinct odd cycle lengths. -/
theorem chromaticNumber_le_of_card_oddCycleLengths_eq (k : ℕ)
    (hk : (oddCycleLengths G).card = k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ) :=
  chromaticNumber_le_of_card_oddCycleLengths_le G k hk.le

/-- The zero-length-set case is two-colorable, including disconnected graphs. -/
theorem isBipartite_of_oddCycleLengths_eq_empty
    (h : oddCycleLengths G = ∅) : G.IsBipartite :=
  isBipartite_of_odd_lengths_empty_independent h

/-- A finite simple graph is bipartite exactly when it has no odd simple cycles. -/
theorem isBipartite_iff_oddCycleLengths_eq_empty :
    G.IsBipartite ↔ oddCycleLengths G = ∅ :=
  ⟨oddCycleLengths_eq_empty_of_bipartite, isBipartite_of_oddCycleLengths_eq_empty G⟩

/-- The same numerical theorem in the form quoted as Theorem 1.1 by
Gao, Huo, and Ma: chromatic number `r + 1` forces `r / 2` distinct odd lengths. -/
theorem card_oddCycleLengths_ge_of_chromaticNumber_eq (r : ℕ)
    (hχ : G.chromaticNumber = (r + 1 : ℕ)) :
    r / 2 ≤ (oddCycleLengths G).card := by
  have h := chromaticNumber_le_two_mul_oddCycleLengths_card_add_two G
  rw [hχ] at h
  have hn := ENat.natCast_le_natCast.mp h
  omega

end JSP000078
