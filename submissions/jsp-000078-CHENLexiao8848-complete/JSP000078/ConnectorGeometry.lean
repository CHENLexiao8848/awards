import JSP000078.MarkedConnectorData
import JSP000078.OutsideHubData
import JSP000078.AttachmentCycles

/-!
# Graph witnesses for marked-cycle connector data

Every selected outside route combines with each proper marked cycle arc.
The connector of length two comes from a single outside endpoint.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An odd marked-distance/connector sum is realized by a simple cycle.
The connector family consists of the two-edge hub route and every chosen
outside route with its two attachment edges. -/
theorem marked_distance_connector_mem {c A B : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hA : A ∉ C.support) (hAB : A ≠ B)
    (X : Finset V) (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x)
    (R : Finset ℕ)
    (hR : ∀ h ∈ R, ∃ P : G.Walk A B, P.IsPath ∧ P.length = h ∧
      Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    {a d t : ℕ} (ha : a ∈ X.image (cyclePosition C))
    (hd : d ∈ properDistances (X.image (cyclePosition C)) C.length a)
    (ht : t ∈ insert 2 (R.image fun h ↦ h + 2)) (hodd : Odd (d + t)) :
    d + t ∈ oddCycleLengths G := by
  classical
  rcases Finset.mem_insert.mp ht with rfl | ht
  · have hdOdd : Odd d := by
      rw [Nat.odd_iff] at hodd ⊢
      omega
    exact (outside_hub_distance_memberships hC hCO hA X
      (fun x hx ↦ ⟨(hX x hx).1, (hX x hx).2.1⟩) ha hd).1 hdOdd
  · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨P, hP, hPlen, hPC⟩ := hR h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    have hmarkbounds : ∀ z ∈ X.image (cyclePosition C), z < C.length := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact cyclePosition_lt hC (hX y hy).1
    have hbounds := properDistances_bounds (X.image (cyclePosition C)) hmarkbounds
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩) d hd
    obtain ⟨y, hy, _, hdy⟩ := exists_vertex_of_proper_cycle_positions hC X
      (fun z hz ↦ (hX z hz).1) hx hd
    let Cx := C.rotate x (hX x hx).1
    have hCx : Cx.IsCycle := hC.rotate (hX x hx).1
    have hCxlen : Cx.length = C.length := C.length_rotate x (hX x hx).1
    have hPCx : Disjoint {v | v ∈ P.support} {v | v ∈ Cx.support} := by
      apply Set.disjoint_left.mpr
      intro v hvP hvC
      exact Set.disjoint_left.mp hPC hvP ((C.mem_support_rotate_iff x (hX x hx).1).mp hvC)
    have hyCx : y ∈ Cx.support :=
      (C.mem_support_rotate_iff x (hX x hx).1).mpr (hX y hy).1
    have hget : Cx.getVert d = y := by
      rw [← hdy]
      exact getVert_cyclePosition Cx hyCx
    have hAyd : G.Adj A (Cx.getVert d) := by simpa only [hget] using (hX y hy).2.1
    obtain ⟨E, _, hE, _, hEL, _⟩ := exists_attachment_cycles_at_index hP hAB hCx hPCx
      hbounds.1 (by omega) hAyd (hX x hx).2.2
    have hEL' : E.length = d + (h + 2) := by omega
    exact (mem_oddCycleLengths G).mpr ⟨hodd, A, E, hE, hEL'⟩

/-- Construct marked connector data from an odd cycle, selected common
neighbors, and a finite family of actual simple outside route lengths. -/
noncomputable def markedConnectorDataOfRoutes {c A B : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hA : A ∉ C.support) (hAB : A ≠ B)
    (X : Finset V) (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x)
    (R : Finset ℕ)
    (hR : ∀ h ∈ R, ∃ P : G.Walk A B, P.IsPath ∧ P.length = h ∧
      Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (k : ℕ) (hk : 2 ≤ k) (hcard : X.card = 2 * k - 1)
    (hK : (oddCycleLengths G).card = k) : MarkedConnectorData where
  circumference := C.length
  parameter := k
  marks := X.image (cyclePosition C)
  lengths := oddCycleLengths G
  connectors := insert 2 (R.image fun h ↦ h + 2)
  circumference_odd := hCO
  parameter_ge_two := hk
  mark_bounds := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact cyclePosition_lt hC (hX x hx).1
  mark_card := by
    rw [Finset.card_image_of_injOn, hcard]
    intro x hx y hy hxy
    exact cyclePosition_injOn C (hX x hx).1 (hX y hy).1 hxy
  length_card := hK
  connector_two := Finset.mem_insert_self _ _
  connector_pos := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · omega
    · obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp ht
      omega
  cycle_membership := fun _ ha _ hd _ ht ho ↦
    marked_distance_connector_mem hC hCO hA hAB X hX R hR ha hd ht ho

/-- The data constructor retains all sets and parameters exactly. -/
theorem markedConnectorDataOfRoutes_fields {c A B : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hA : A ∉ C.support) (hAB : A ≠ B)
    (X : Finset V) (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x)
    (R : Finset ℕ)
    (hR : ∀ h ∈ R, ∃ P : G.Walk A B, P.IsPath ∧ P.length = h ∧
      Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (k : ℕ) (hk : 2 ≤ k) (hcard : X.card = 2 * k - 1)
    (hK : (oddCycleLengths G).card = k) :
    let M := markedConnectorDataOfRoutes hC hCO hA hAB X hX R hR k hk hcard hK
    M.circumference = C.length ∧ M.parameter = k ∧ M.marks = X.image (cyclePosition C) ∧
      M.lengths = oddCycleLengths G ∧ M.connectors = insert 2 (R.image fun h ↦ h + 2) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end JSP000078
