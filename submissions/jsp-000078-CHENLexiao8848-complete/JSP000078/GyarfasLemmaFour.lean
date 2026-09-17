import JSP000078.EndpointRoutes
import JSP000078.EndpointCount
import JSP000078.AttachmentCycles
import JSP000078.EndpointConfigurationBridge

/-!
# Gyárfás's endpoint-neighbor count

Individual cycle constructions discharge every field of the arithmetic data.
The complementary construction counts both attachment edges, correcting the
intermediate printed formula while preserving the published lower bound.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The graph configuration realizes the two complementary mixed cycle lengths. -/
theorem EndpointConfiguration.exists_mixed_cycles (E : EndpointConfiguration G)
    {u t : ℕ} (hu : u ∈ E.routeLengths) (ht : t ∈ E.attachments) :
    ∃ C D : G.Walk E.first E.first, C.IsCycle ∧ D.IsCycle ∧
      C.length = u + t + 2 ∧ D.length = u + (E.cycle.length - t) + 2 := by
  obtain ⟨P, hP, hPL, hsub⟩ := E.exists_route hu
  have hPC : Disjoint {v | v ∈ P.support} {v | v ∈ E.cycle.support} :=
    Set.disjoint_left.mpr fun v hvP hvC ↦ Set.disjoint_left.mp E.disjoint (hsub hvP) hvC
  obtain ⟨C, D, hC, hD, hCL, hDL⟩ := exists_attachment_cycles_at_index hP E.ends_ne
    E.longest.1 hPC (E.attachment_bounds t ht).1 (E.attachment_bounds t ht).2
    (E.first_attachments t ht) E.last_attachment
  exact ⟨C, D, hC, hD, by omega, by omega⟩

/-- Construct the length data from actual simple cycles and their maximum. -/
noncomputable def EndpointConfiguration.toLengthData (E : EndpointConfiguration G) :
    EndpointCycleData where
  bound := E.cycle.length
  tailLength := E.tailLength
  outsideLengths := E.routeLengths
  attachmentLengths := E.attachments
  oddLengths := oddCycleLengths G
  bound_odd := E.longest.2.1
  attachment_nonempty := E.attachments_nonempty
  attachment_bounds := E.attachment_bounds
  outside_lower := fun u hu ↦ E.route_lower hu
  outside_min_mem := E.route_min_mem
  max_odd := by
    intro n hn
    obtain ⟨hOdd, c, C, hC, rfl⟩ := (mem_oddCycleLengths G).mp hn
    exact E.longest.2.2 c C hC hOdd
  low_cycle := by
    intro u hu hEven
    obtain ⟨C, hC, hCL⟩ := E.exists_low_cycle hu hEven
    exact (mem_oddCycleLengths G).mpr
      ⟨hEven.add_odd odd_one, E.first, C, hC, hCL⟩
  direct_cycle := by
    intro u hu t ht hOdd
    obtain ⟨C, D, hC, _, hCL, _⟩ := E.exists_mixed_cycles hu ht
    exact (mem_oddCycleLengths G).mpr ⟨hOdd, E.first, C, hC, hCL⟩
  complementary_cycle := by
    intro u hu t ht hOdd
    obtain ⟨C, D, _, hD, _, hDL⟩ := E.exists_mixed_cycles hu ht
    exact (mem_oddCycleLengths G).mpr ⟨hOdd, E.first, D, hD, hDL⟩

/-- Gyárfás Lemma 4 in its nonempty-attachment configuration: the number
of outside chords plus half the cycle attachments, rounded up, is a lower
bound on the number of distinct odd cycle lengths. -/
theorem EndpointConfiguration.odd_lengths_lower_bound (E : EndpointConfiguration G) :
    E.chords.card + (E.attachments.card + 1) / 2 ≤ (oddCycleLengths G).card := by
  have h := E.toLengthData.length_count
  change E.routeLengths.card - 1 + (E.attachments.card + 1) / 2 ≤
    (oddCycleLengths G).card at h
  rw [E.card_routeLengths] at h
  simpa only [Nat.add_sub_cancel] using h

/-- The exact endpoint-counting proposition is discharged by graph constructions. -/
theorem historicalEndpointNeighborCount : HistoricalEndpointNeighborCount := by
  intro V _ G E
  exact E.odd_lengths_lower_bound

/-- The source lemma for arbitrary selected neighbor vertices: no cycle
base, orientation, or path-position representation is imposed on the caller. -/
theorem odd_lengths_of_endpoint_neighbor_sets {c A B y : V}
    {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hy : y ∈ C.support) (hBy : G.Adj B y) (X Z : Finset V) (hXne : X.Nonempty)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ v ≠ y ∧ G.Adj A v)
    (hZ : ∀ v ∈ Z, v ∈ P.support ∧ v ≠ P.getVert 1 ∧ G.Adj A v) :
    Z.card + (X.card + 1) / 2 ≤ (oddCycleLengths G).card := by
  obtain ⟨E, hXcard, hZcard⟩ := exists_endpointConfiguration_of_neighbor_sets
    hC hP hAB hPC hy hBy X Z hXne hX hZ
  simpa only [hXcard, hZcard] using E.odd_lengths_lower_bound

end JSP000078
