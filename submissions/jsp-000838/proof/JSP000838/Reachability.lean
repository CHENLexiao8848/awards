import JSP000838.Orientation

namespace JSP000838

open Relation

variable {V : Type*}

/-- The reachability partial order of an acyclic relation. Its strict relation is
the nonempty transitive closure; its nonstrict relation includes the empty path. -/
@[instance_reducible]
def reachabilityOrder (D : V → V → Prop) (hD : Acyclic D) : PartialOrder V where
  le := ReflTransGen D
  lt := TransGen D
  le_refl _ := .refl
  le_trans _ _ _ := ReflTransGen.trans
  le_antisymm a b hab hba := by
    rcases reflTransGen_iff_eq_or_transGen.mp hab with heq | hp
    · exact heq.symm
    · exact False.elim (hD a (hp.trans_left hba))
  lt_iff_le_not_ge a b := by
    constructor
    · intro hab
      exact ⟨hab.to_reflTransGen, fun hba => hD a (hab.trans_left hba)⟩
    · rintro ⟨hab, hba⟩
      rcases reflTransGen_iff_eq_or_transGen.mp hab with heq | hp
      · subst b
        exact False.elim (hba .refl)
      · exact hp

theorem reachabilityOrder_le (D : V → V → Prop) (hD : Acyclic D) (u v : V) :
    @LE.le V (reachabilityOrder D hD).toLE u v ↔ ReflTransGen D u v := Iff.rfl

theorem reachabilityOrder_lt (D : V → V → Prop) (hD : Acyclic D) (u v : V) :
    @LT.lt V (reachabilityOrder D hD).toLT u v ↔ TransGen D u v := Iff.rfl

/-- Every cover in a reachability order is already an original arc. -/
theorem covBy_reachabilityOrder_implies_edge {D : V → V → Prop} (hD : Acyclic D)
    {u v : V} (huv : @CovBy V (reachabilityOrder D hD).toLT u v) : D u v := by
  change TransGen D u v ∧ (∀ ⦃w⦄, TransGen D u w → ¬ TransGen D w v) at huv
  rcases huv with ⟨hp, hcover⟩
  cases hp with
  | single h => exact h
  | tail huw hwv => exact False.elim (hcover huw (.single hwv))

end JSP000838
