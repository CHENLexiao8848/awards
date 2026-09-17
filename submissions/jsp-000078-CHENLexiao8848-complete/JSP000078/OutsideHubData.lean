import JSP000078.HubDistanceData
import JSP000078.CycleDistanceCoordinates
import JSP000078.OutsideVertexCycles

/-!
# Realizing cyclic hub distance data in a graph

Selected neighbors of a vertex outside an odd cycle give canonical marked
positions. Every proper distance after any change of base corresponds
to a simple arc and two hub spokes, so the abstract distance data's cycle
memberships are discharged by actual graph cycles.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A proper marked distance from the position of `x` is the rotated
coordinate of another selected vertex. -/
theorem exists_vertex_of_proper_cycle_positions {c x : V} {C : G.Walk c c}
    (hC : C.IsCycle) (X : Finset V) (hX : ∀ y ∈ X, y ∈ C.support)
    (hx : x ∈ X) {d : ℕ}
    (hd : d ∈ properDistances (X.image (cyclePosition C)) C.length (cyclePosition C x)) :
    ∃ y ∈ X, y ≠ x ∧ cyclePosition (C.rotate x (hX x hx)) y = d := by
  obtain ⟨b, hb, hbd⟩ := Finset.mem_image.mp hd
  obtain ⟨hbx, hbX⟩ := Finset.mem_erase.mp hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbX
  refine ⟨y, hy, ?_, ?_⟩
  · intro hyx
    exact hbx (hyx ▸ rfl)
  · exact (cyclePosition_rotate hC (hX x hx) (hX y hy)).trans hbd

variable [Fintype V]

/-- Every proper distance between selected neighbors of an outside hub
supplies the appropriate forward or complementary odd cycle length. -/
theorem outside_hub_distance_memberships {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hv : v ∉ C.support)
    (X : Finset V) (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj v x)
    {a d : ℕ} (ha : a ∈ X.image (cyclePosition C))
    (hd : d ∈ properDistances (X.image (cyclePosition C)) C.length a) :
    (Odd d → d + 2 ∈ oddCycleLengths G) ∧
      (Even d → C.length - d + 2 ∈ oddCycleLengths G) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  have hmarkbounds : ∀ z ∈ X.image (cyclePosition C), z < C.length := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact cyclePosition_lt hC (hX y hy).1
  have hbounds := properDistances_bounds (X.image (cyclePosition C)) hmarkbounds
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩) d hd
  obtain ⟨y, hy, _, hdy⟩ := exists_vertex_of_proper_cycle_positions hC X
    (fun z hz ↦ (hX z hz).1) hx hd
  let R := C.rotate x (hX x hx).1
  have hR : R.IsCycle := hC.rotate (hX x hx).1
  have hRlen : R.length = C.length := C.length_rotate x (hX x hx).1
  have hvR : v ∉ R.support := fun h ↦
    hv ((C.mem_support_rotate_iff x (hX x hx).1).mp h)
  have hyR : y ∈ R.support :=
    (C.mem_support_rotate_iff x (hX x hx).1).mpr (hX y hy).1
  have hget : R.getVert d = y := by
    rw [← hdy]
    exact getVert_cyclePosition R hyR
  have hvd : G.Adj v (R.getVert d) := by simpa only [hget] using (hX y hy).2
  constructor
  · intro hOdd
    exact outside_vertex_forward_length_mem hR hvR hbounds.1
      (by omega) (hX x hx).2 hvd (hOdd.add_even even_two)
  · intro hEven
    have hOddLength : Odd (R.length - d + 2) := by
      have hnmod := Nat.odd_iff.mp hCO
      have hdmod := Nat.even_iff.mp hEven
      rw [Nat.odd_iff]
      omega
    simpa only [hRlen] using outside_vertex_complement_length_mem hR hvR hbounds.1
      (by omega) (hX x hx).2 hvd hOddLength

/-- Construct the abstract hub data entirely from selected graph neighbors
and actual odd simple-cycle memberships. -/
noncomputable def outsideHubData {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hv : v ∉ C.support)
    (X : Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hcard : X.card = 2 * k) (hKcard : (oddCycleLengths G).card = k)
    (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj v x) : HubDistanceData where
  circumference := C.length
  parameter := k
  marks := X.image (cyclePosition C)
  lengths := oddCycleLengths G
  circumference_odd := hCO
  parameter_pos := hk
  mark_bounds := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact cyclePosition_lt hC (hX x hx).1
  mark_card := by
    rw [Finset.card_image_of_injOn, hcard]
    intro x hx y hy hxy
    exact cyclePosition_injOn C (hX x hx).1 (hX y hy).1 hxy
  length_card := hKcard
  circumference_mem := (mem_oddCycleLengths G).mpr ⟨hCO, c, C, hC, rfl⟩
  odd_cycle := fun _ ha _ hd ↦ (outside_hub_distance_memberships hC hCO hv X hX ha hd).1
  even_cycle := fun _ ha _ hd ↦ (outside_hub_distance_memberships hC hCO hv X hX ha hd).2

end JSP000078
