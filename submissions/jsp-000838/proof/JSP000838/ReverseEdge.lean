import JSP000838.Orientation

namespace JSP000838

open Relation

variable {V : Type*} {D : V → V → Prop} {u v a b w : V}

/-- A directed path either survives reversal, or traverses the deleted arc. -/
theorem transGen_reverseEdge_or_factor (h : TransGen D a b) :
    TransGen (reverseEdge D u v) a b ∨
      (ReflTransGen D a u ∧ ReflTransGen D v b) := by
  induction h with
  | @single b hab =>
      by_cases heq : a = u ∧ b = v
      · rcases heq with ⟨rfl, rfl⟩
        exact Or.inr ⟨.refl, .refl⟩
      · exact Or.inl (.single (Or.inl ⟨hab, heq⟩))
  | @tail b c hab hbc ih =>
      by_cases heq : b = u ∧ c = v
      · rcases heq with ⟨rfl, rfl⟩
        exact Or.inr ⟨hab.to_reflTransGen, .refl⟩
      · rcases ih with h | ⟨hau, hvb⟩
        · exact Or.inl (h.tail (Or.inl ⟨hbc, heq⟩))
        · exact Or.inr ⟨hau, hvb.tail hbc⟩

/-- If an arc has a directed route through a strict intermediate vertex, reversing
it creates a nonempty directed closed walk. Acyclicity forces both subpaths to
avoid the reversed arc. -/
theorem reverseEdge_not_acyclic_of_intermediate (hD : Acyclic D)
    (huw : TransGen D u w) (hwv : TransGen D w v) :
    ¬ Acyclic (reverseEdge D u v) := by
  have hp : TransGen (reverseEdge D u v) u w := by
    rcases transGen_reverseEdge_or_factor huw with hp | ⟨_, hvw⟩
    · exact hp
    · exact False.elim (hD v (TransGen.trans_right hvw hwv))
  have hq : TransGen (reverseEdge D u v) w v := by
    rcases transGen_reverseEdge_or_factor hwv with hq | ⟨hwu, _⟩
    · exact hq
    · exact False.elim (hD u (huw.trans_left hwu))
  intro hrev
  exact hrev u ((hp.trans hq).tail (reverseEdge_backward u v))

theorem IsRobustAcyclicOrientation.no_intermediate {G : SimpleGraph V}
    (h : IsRobustAcyclicOrientation G D) (huv : D u v) :
    ¬ ∃ w, TransGen D u w ∧ TransGen D w v := by
  rintro ⟨w, huw, hwv⟩
  exact reverseEdge_not_acyclic_of_intermediate h.2.1 huw hwv (h.2.2 u v huv)

end JSP000838
