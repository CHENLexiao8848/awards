import JSP000838.SourceTheorem

namespace JSP000838

/-- Negative resolution of JSP-000838 / Erdős Problem #1006. -/
theorem jsp_000838_counterexample :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), NoShortCycles 5 G ∧
      ∀ D, ¬ IsRobustAcyclicOrientation G D := by
  obtain ⟨G, hcycles, hordered⟩ := exists_noShortCycles_ordered_five
  exact ⟨carrierN, G, hcycles, hordered.not_robust⟩

/-- The universal affirmative conjecture is false. -/
theorem jsp_000838_conjecture_false :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)), NoShortCycles 5 G →
      ∃ D, IsRobustAcyclicOrientation G D) := by
  intro h
  obtain ⟨n, G, hG, hbad⟩ := jsp_000838_counterexample
  obtain ⟨D, hD⟩ := h n G hG
  exact hbad D hD

end JSP000838
