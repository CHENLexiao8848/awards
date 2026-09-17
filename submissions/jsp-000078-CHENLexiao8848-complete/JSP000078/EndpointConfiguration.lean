import JSP000078.LongestOddCycle

/-! # Graph configuration for Gyárfás's endpoint counting lemma -/

namespace JSP000078

open SimpleGraph

/-- An outside simple path with selected incident chords and selected
attachments to a longest odd cycle. The cycle is based at the final
endpoint's attachment vertex, so each selected positive index is its arc
distance from that attachment. -/
structure EndpointConfiguration {V : Type*} [Fintype V] (G : SimpleGraph V) where
  cycleBase : V
  cycle : G.Walk cycleBase cycleBase
  longest : IsLongestOddCycle cycle
  first : V
  last : V
  outside : G.Walk first last
  outside_path : outside.IsPath
  ends_ne : first ≠ last
  disjoint : Disjoint {v | v ∈ outside.support} {v | v ∈ cycle.support}
  last_attachment : G.Adj last cycleBase
  attachments : Finset ℕ
  attachments_nonempty : attachments.Nonempty
  attachment_bounds : ∀ t ∈ attachments, 1 ≤ t ∧ t < cycle.length
  first_attachments : ∀ t ∈ attachments, G.Adj first (cycle.getVert t)
  chords : Finset ℕ
  chord_bounds : ∀ d ∈ chords, 2 ≤ d ∧ d ≤ outside.length
  chord_adj : ∀ d ∈ chords, G.Adj first (outside.getVert d)

/-- The endpoint-neighbor lower bound in its needed nonempty attachment
configuration. No degree or global connectivity premise is required here. -/
def HistoricalEndpointNeighborCount : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (E : EndpointConfiguration G),
    E.chords.card + (E.attachments.card + 1) / 2 ≤ (oddCycleLengths G).card

end JSP000078
