import JSP000078.General

open SimpleGraph

-- Exact original statement, including arbitrary vertex universes and the iff.
example :
    ∀ {V : Type*} (G : SimpleGraph V) (k : ℕ),
      G.oddCycleLengths.Finite →
      G.oddCycleLengths.ncard ≤ k →
        G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
        (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
          (SimpleGraph.completeGraph (Fin (2 * k + 2))).IsContained G) :=
  JSP000078.erdos_58

-- The infinite vertex domain requires no local-finiteness or connectivity premise.
example (G : SimpleGraph ℕ) (k : ℕ) (hfin : G.oddCycleLengths.Finite)
    (hk : G.oddCycleLengths.ncard ≤ k) : G.Colorable (2 * k + 2) :=
  JSP000078.colorable_of_finite_oddCycleLengths G k hfin hk

-- The zero case, on arbitrary vertex types, includes the equality direction.
example {V : Type*} (G : SimpleGraph V) (hfin : G.oddCycleLengths.Finite)
    (hk : G.oddCycleLengths.ncard = 0) :
    G.chromaticNumber ≤ 2 ∧
      (G.chromaticNumber = 2 ↔ (completeGraph (Fin 2)).IsContained G) := by
  simpa using JSP000078.erdos_58 G 0 hfin hk.le

-- Empty types and fewer-than-k lengths use the same finite interface.
example (G : SimpleGraph Empty) : G.Colorable 1 := by
  exact G.colorable_of_fintype.mono (by simp)

example {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : (JSP000078.oddCycleLengths G).card < k) : G.Colorable (2 * k + 1) :=
  (JSP000078.colorable_two_mul_oddCycleLengths_card_add_two G).mono (by omega)

#check @JSP000078.erdos_58
#print axioms JSP000078.erdos_58
#print axioms JSP000078.colorable_of_finite_induced
#print axioms JSP000078.finite_oddCycleLengths_eq
#print axioms JSP000078.induced_oddCycleLengths_subset
#print axioms JSP000078.colorable_of_card_oddCycleLengths_le_of_cliqueFree
#print axioms JSP000078.chromaticNumber_eq_iff_not_cliqueFree_of_card_oddCycleLengths_le
#print axioms JSP000078.colorable_of_finite_oddCycleLengths
#print axioms JSP000078.colorable_of_finite_oddCycleLengths_of_cliqueFree
