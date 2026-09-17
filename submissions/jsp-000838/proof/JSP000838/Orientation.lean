import JSP000838.Defs

namespace JSP000838

variable {V : Type*} {G : SimpleGraph V} {D : V → V → Prop}

theorem IsOrientation.adj (h : IsOrientation G D) {u v : V} (huv : D u v) :
    G.Adj u v :=
  (h.1 u v).2 (Or.inl huv)

theorem IsOrientation.asymm (h : IsOrientation G D) {u v : V} (huv : D u v) :
    ¬ D v u := h.2 u v huv

theorem IsOrientation.irrefl (h : IsOrientation G D) (v : V) : ¬ D v v := by
  intro hv
  exact h.asymm hv hv

theorem IsOrientation.ne (h : IsOrientation G D) {u v : V} (huv : D u v) : u ≠ v := by
  rintro rfl
  exact h.irrefl u huv

theorem Acyclic.irrefl (h : Acyclic D) (v : V) : ¬ D v v := by
  intro hv
  exact h v (.single hv)

theorem Acyclic.ne (h : Acyclic D) {u v : V} (huv : Relation.TransGen D u v) :
    u ≠ v := by
  rintro rfl
  exact h u huv

theorem Acyclic.asymm (h : Acyclic D) {u v : V} (huv : Relation.TransGen D u v) :
    ¬ Relation.TransGen D v u := by
  intro hvu
  exact h u (huv.trans hvu)

theorem reverseEdge_backward (u v : V) : reverseEdge D u v v u :=
  Or.inr ⟨rfl, rfl⟩

theorem reverseEdge_forward {u v : V} (huv : u ≠ v) : ¬ reverseEdge D u v u v := by
  simp [reverseEdge, huv]

theorem reverseEdge_unchanged {u v x y : V}
    (hforward : ¬ (x = u ∧ y = v)) (hbackward : ¬ (x = v ∧ y = u)) :
    reverseEdge D u v x y ↔ D x y := by
  simp [reverseEdge, hforward, hbackward]

theorem IsOrientation.reverseEdge (h : IsOrientation G D) {u v : V} (huv : D u v) :
    IsOrientation G (reverseEdge D u v) := by
  have hne := h.ne huv
  constructor
  · intro x y
    have hadj := h.1 x y
    have hxy := h.2 x y
    have hyx := h.2 y x
    have hvu := h.2 u v huv
    simp only [JSP000838.reverseEdge]
    grind
  · intro x y
    have hxy := h.2 x y
    have hyx := h.2 y x
    have hvu := h.2 u v huv
    simp only [JSP000838.reverseEdge]
    grind

theorem reverseEdge_involutive (h : IsOrientation G D) {u v : V} (huv : D u v) :
    reverseEdge (reverseEdge D u v) v u = D := by
  funext x y
  apply propext
  have hne := h.ne huv
  have hvu := h.asymm huv
  simp only [reverseEdge]
  grind

end JSP000838
