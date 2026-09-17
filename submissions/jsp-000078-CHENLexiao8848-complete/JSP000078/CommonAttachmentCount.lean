import JSP000078.CommonAttachmentData
import Mathlib.Data.Finset.Max

/-! # Extra lengths from common attachment vertices -/

namespace JSP000078

/-- With an odd outside path and even arcs, its shared-vertex cycle is
strictly shorter than every translated arc cycle. -/
theorem CommonAttachmentData.count_of_odd_path (D : CommonAttachmentData)
    (hpath : Odd D.pathLength) (harcs : ∀ t ∈ D.arcLengths, Even t) :
    D.arcLengths.card + 1 ≤ D.oddLengths.card := by
  let T := D.arcLengths.image fun t ↦ t + D.pathLength + 2
  have hTcard : T.card = D.arcLengths.card := Finset.card_image_of_injOn (by
    intro a _ b _ heq
    change a + D.pathLength + 2 = b + D.pathLength + 2 at heq
    omega)
  have hTsub : T ⊆ D.oddLengths := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact D.mixed t ht (((harcs t ht).add_odd hpath).add_even even_two)
  have hbase := D.shared (hpath.add_even even_two)
  have hnot : D.pathLength + 2 ∉ T := by
    intro h
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp h
    have := D.arc_pos t ht
    omega
  have hcard := Finset.card_le_card (Finset.insert_subset hbase hTsub)
  rw [Finset.card_insert_of_notMem hnot, hTcard] at hcard
  exact hcard

/-- With an even positive outside path and odd arcs, the largest translated
arc cycle is strictly longer than all cycles using only one outside vertex. -/
theorem CommonAttachmentData.count_of_even_path (D : CommonAttachmentData)
    (hpath : Even D.pathLength) (harcs : ∀ t ∈ D.arcLengths, Odd t) :
    D.arcLengths.card + 1 ≤ D.oddLengths.card := by
  let T := D.arcLengths.image fun t ↦ t + 2
  let m := D.arcLengths.max' D.arc_nonempty
  have hm : m ∈ D.arcLengths := D.arcLengths.max'_mem D.arc_nonempty
  have hTcard : T.card = D.arcLengths.card := Finset.card_image_of_injOn (by
    intro a _ b _ heq
    change a + 2 = b + 2 at heq
    omega)
  have hTsub : T ⊆ D.oddLengths := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact D.direct t ht ((harcs t ht).add_even even_two)
  have hnew := D.mixed m hm (((harcs m hm).add_even hpath).add_even even_two)
  have hnot : m + D.pathLength + 2 ∉ T := by
    intro h
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp h
    have htm : t ≤ m := D.arcLengths.le_max' t ht
    have := D.path_pos
    omega
  have hcard := Finset.card_le_card (Finset.insert_subset hnew hTsub)
  rw [Finset.card_insert_of_notMem hnot, hTcard] at hcard
  exact hcard

end JSP000078
