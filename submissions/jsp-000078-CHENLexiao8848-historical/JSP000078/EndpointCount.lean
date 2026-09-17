import JSP000078.EndpointCycleData
import JSP000078.SeparatedSumCounting
import JSP000078.EndpointCountArithmetic

/-!
# Counting the endpoint cycle lengths

The short cycles lie strictly below a high sumset: reversing the attachment
arc would otherwise create an odd cycle longer than the prescribed bound.
Counting a nonempty attachment parity class then gives the endpoint estimate.
-/

namespace JSP000078

namespace EndpointCycleData

/-- A nonempty attachment class gives a counting bound whenever its high
lengths and complementary low-index lengths are realized and the two
attachment contributions sum to `bound + 4`. -/
theorem count_attachment_class (D : EndpointCycleData)
    (T : Finset ℕ) (hT : T.Nonempty) (δ δstar : ℕ → ℕ)
    (hinj : Set.InjOn δ T)
    (hhigh : ∀ v ∈ D.outsideLengths, ¬Even (v - D.tailLength) →
      ∀ t ∈ T, v + δ t ∈ D.oddLengths)
    (halt : ∀ u ∈ D.outsideLengths, Even (u - D.tailLength) →
      ∀ t ∈ T, u + δstar t ∈ D.oddLengths)
    (hadd : ∀ t ∈ T, δ t + δstar t = D.bound + 4) :
    D.outsideLengths.card - 1 + T.card ≤ D.oddLengths.card := by
  classical
  let I := D.outsideLengths.filter fun u ↦ Even (u - D.tailLength)
  let J := D.outsideLengths.filter fun u ↦ ¬Even (u - D.tailLength)
  have hJ : J.Nonempty := by
    refine ⟨D.tailLength + 1, Finset.mem_filter.mpr ⟨D.outside_min_mem, ?_⟩⟩
    simp
  have hU : 1 ≤ D.outsideLengths.card :=
    Finset.card_pos.mpr ⟨D.tailLength + 1, D.outside_min_mem⟩
  have hpartition : I.card + J.card = (D.outsideLengths.card - 1) + 1 := by
    have h := D.outsideLengths.card_filter_add_card_filter_not
      (fun u ↦ Even (u - D.tailLength))
    dsimp only [I, J]
    omega
  have hcard : (T.image δ).card = T.card := Finset.card_image_of_injOn hinj
  have hcount := add_card_le_of_separated_sumset_partition
    I J (T.image δ) D.oddLengths (D.outsideLengths.card - 1) hpartition hJ
    (hT.image δ) (fun u ↦ u - D.tailLength + 1) ?_ ?_ ?_ ?_
  · simpa only [hcard] using hcount
  · intro u hu v hv heq
    have huLower := D.outside_lower u (Finset.mem_filter.mp hu).1
    have hvLower := D.outside_lower v (Finset.mem_filter.mp hv).1
    change u - D.tailLength + 1 = v - D.tailLength + 1 at heq
    omega
  · intro u hu
    obtain ⟨huU, huEven⟩ := Finset.mem_filter.mp hu
    exact D.low_cycle u huU huEven
  · intro v hv d hd
    obtain ⟨hvU, hvOdd⟩ := Finset.mem_filter.mp hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    exact hhigh v hvU hvOdd t ht
  · intro u hu v hv d hd
    obtain ⟨huU, huEven⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvU, _⟩ := Finset.mem_filter.mp hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    have hmax := D.max_odd _ (halt u huU huEven t ht)
    have hsum := hadd t ht
    have huLower := D.outside_lower u huU
    have hvLower := D.outside_lower v hvU
    change u - D.tailLength + 1 < v + δ t
    omega

/-- Attachments with the same parity as the terminal segment use the
direct arc for the high family and the complementary arc for separation. -/
theorem count_same_parity_attachments (D : EndpointCycleData)
    (hT : (D.attachmentLengths.filter fun t ↦ t % 2 = D.tailLength % 2).Nonempty) :
    D.outsideLengths.card - 1 +
      (D.attachmentLengths.filter fun t ↦ t % 2 = D.tailLength % 2).card ≤
        D.oddLengths.card := by
  classical
  apply D.count_attachment_class _ hT (fun t ↦ t + 2) (fun t ↦ D.bound - t + 2)
  · intro t _ s _ heq
    change t + 2 = s + 2 at heq
    omega
  · intro v hv hvOdd t ht
    obtain ⟨htT, hpar⟩ := Finset.mem_filter.mp ht
    have hvLower := D.outside_lower v hv
    have hvpar : (v - D.tailLength) % 2 ≠ 0 := by
      simpa only [Nat.even_iff] using hvOdd
    have hodd : Odd (v + t + 2) := by
      rw [Nat.odd_iff]
      omega
    simpa only [Nat.add_assoc] using D.direct_cycle v hv t htT hodd
  · intro u hu huEven t ht
    obtain ⟨htT, hpar⟩ := Finset.mem_filter.mp ht
    have huLower := D.outside_lower u hu
    have htBound := (D.attachment_bounds t htT).2
    have hupar := Nat.even_iff.mp huEven
    have hNpar := Nat.odd_iff.mp D.bound_odd
    have hodd : Odd (u + (D.bound - t) + 2) := by
      rw [Nat.odd_iff]
      omega
    simpa only [Nat.add_assoc] using D.complementary_cycle u hu t htT hodd
  · intro t ht
    have htBound := (D.attachment_bounds t (Finset.mem_filter.mp ht).1).2
    omega

/-- Attachments of opposite parity use the complementary arc for the high
family and the direct arc for separation. -/
theorem count_opposite_parity_attachments (D : EndpointCycleData)
    (hT : (D.attachmentLengths.filter fun t ↦ ¬t % 2 = D.tailLength % 2).Nonempty) :
    D.outsideLengths.card - 1 +
      (D.attachmentLengths.filter fun t ↦ ¬t % 2 = D.tailLength % 2).card ≤
        D.oddLengths.card := by
  classical
  apply D.count_attachment_class _ hT (fun t ↦ D.bound - t + 2) (fun t ↦ t + 2)
  · intro t ht s hs heq
    have htBound := (D.attachment_bounds t (Finset.mem_filter.mp ht).1).2
    have hsBound := (D.attachment_bounds s (Finset.mem_filter.mp hs).1).2
    change D.bound - t + 2 = D.bound - s + 2 at heq
    omega
  · intro v hv hvOdd t ht
    obtain ⟨htT, hpar⟩ := Finset.mem_filter.mp ht
    have hvLower := D.outside_lower v hv
    have htBound := (D.attachment_bounds t htT).2
    have hvpar : (v - D.tailLength) % 2 ≠ 0 := by
      simpa only [Nat.even_iff] using hvOdd
    have hNpar := Nat.odd_iff.mp D.bound_odd
    have hodd : Odd (v + (D.bound - t) + 2) := by
      rw [Nat.odd_iff]
      omega
    simpa only [Nat.add_assoc] using D.complementary_cycle v hv t htT hodd
  · intro u hu huEven t ht
    obtain ⟨htT, hpar⟩ := Finset.mem_filter.mp ht
    have huLower := D.outside_lower u hu
    have hupar := Nat.even_iff.mp huEven
    have hodd : Odd (u + t + 2) := by
      rw [Nat.odd_iff]
      omega
    simpa only [Nat.add_assoc] using D.direct_cycle u hu t htT hodd
  · intro t ht
    have htBound := (D.attachment_bounds t (Finset.mem_filter.mp ht).1).2
    omega

/-- The endpoint length constraints force the source's ceiling bound. -/
theorem length_count (D : EndpointCycleData) :
    D.outsideLengths.card - 1 + (D.attachmentLengths.card + 1) / 2 ≤ D.oddLengths.card := by
  classical
  apply max_count_half_of_nonempty_classes D.attachmentLengths.card
    (D.outsideLengths.card - 1)
    (D.attachmentLengths.filter fun t ↦ t % 2 = D.tailLength % 2).card
    (D.attachmentLengths.filter fun t ↦ ¬t % 2 = D.tailLength % 2).card D.oddLengths.card
  · exact Finset.card_pos.mpr D.attachment_nonempty
  · exact D.attachmentLengths.card_filter_add_card_filter_not
      (fun t ↦ t % 2 = D.tailLength % 2)
  · intro hpos
    exact D.count_same_parity_attachments (Finset.card_pos.mp hpos)
  · intro hpos
    exact D.count_opposite_parity_attachments (Finset.card_pos.mp hpos)

end EndpointCycleData

/-- The precise counting obligation for Gyárfás's Lemma 4 is proved from
individual cycle memberships and maximality, without a cardinality premise. -/
theorem historicalEndpointLengthCount : HistoricalEndpointLengthCount :=
  EndpointCycleData.length_count

end JSP000078
