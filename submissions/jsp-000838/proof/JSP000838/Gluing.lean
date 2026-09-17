import Mathlib.Combinatorics.SimpleGraph.Basic

namespace JSP000838.Gluing

variable {V : Type*}

def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False

def FourCycleFree (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

private theorem edge_ne {G : SimpleGraph V} {x y : V} (h : G.Adj x y) : x ≠ y := by
  intro hxy
  subst y
  exact G.irrefl h

theorem triangleFree_sup (G H : SimpleGraph V) (S : Set V)
    (hG : TriangleFree G) (hH : TriangleFree H)
    (hsupp : ∀ ⦃x y⦄, H.Adj x y → x ∈ S ∧ y ∈ S)
    (hsep1 : ∀ x y, x ∈ S → y ∈ S → G.Adj x y → False)
    (hsep2 : ∀ x y z, x ∈ S → y ∈ S → x ≠ y → G.Adj x z → G.Adj z y → False) :
    TriangleFree (G ⊔ H) := by
  intro a b c hab hbc hca
  change G.Adj a b ∨ H.Adj a b at hab
  change G.Adj b c ∨ H.Adj b c at hbc
  change G.Adj c a ∨ H.Adj c a at hca
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc <;> rcases hca with hca | hca
  · exact hG a b c hab hbc hca
  · exact hsep2 a c b (hsupp hca).2 (hsupp hca).1 (Ne.symm (edge_ne hca)) hab hbc
  · exact hsep2 c b a (hsupp hbc).2 (hsupp hbc).1 (Ne.symm (edge_ne hbc)) hca hab
  · exact hsep1 a b (hsupp hca).2 (hsupp hbc).1 hab
  · exact hsep2 b a c (hsupp hab).2 (hsupp hab).1 (Ne.symm (edge_ne hab)) hbc hca
  · exact hsep1 b c (hsupp hab).2 (hsupp hca).1 hbc
  · exact hsep1 c a (hsupp hbc).2 (hsupp hab).1 hca
  · exact hH a b c hab hbc hca

theorem fourCycleFree_sup (G H : SimpleGraph V) (S : Set V)
    (hG : FourCycleFree G) (hH : FourCycleFree H)
    (hsupp : ∀ ⦃x y⦄, H.Adj x y → x ∈ S ∧ y ∈ S)
    (hsep1 : ∀ x y, x ∈ S → y ∈ S → G.Adj x y → False)
    (hsep2 : ∀ x y z, x ∈ S → y ∈ S → x ≠ y → G.Adj x z → G.Adj z y → False)
    (hsep3 : ∀ x y z w, x ∈ S → y ∈ S → x ≠ y →
      G.Adj x z → G.Adj z w → G.Adj w y → False) : FourCycleFree (G ⊔ H) := by
  intro a b c d hac hbd hab hbc hcd hda
  change G.Adj a b ∨ H.Adj a b at hab
  change G.Adj b c ∨ H.Adj b c at hbc
  change G.Adj c d ∨ H.Adj c d at hcd
  change G.Adj d a ∨ H.Adj d a at hda
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc <;>
    rcases hcd with hcd | hcd <;> rcases hda with hda | hda
  · exact hG a b c d hac hbd hab hbc hcd hda
  · exact hsep3 a d b c (hsupp hda).2 (hsupp hda).1 (Ne.symm (edge_ne hda)) hab hbc hcd
  · exact hsep3 d c a b (hsupp hcd).2 (hsupp hcd).1 (Ne.symm (edge_ne hcd)) hda hab hbc
  · exact hsep2 a c b (hsupp hda).2 (hsupp hcd).1 hac hab hbc
  · exact hsep3 c b d a (hsupp hbc).2 (hsupp hbc).1 (Ne.symm (edge_ne hbc)) hcd hda hab
  · exact hsep1 a b (hsupp hda).2 (hsupp hbc).1 hab
  · exact hsep2 d b a (hsupp hcd).2 (hsupp hbc).1 (Ne.symm hbd) hda hab
  · exact hsep1 a b (hsupp hda).2 (hsupp hbc).1 hab
  · exact hsep3 b a c d (hsupp hab).2 (hsupp hab).1 (Ne.symm (edge_ne hab)) hbc hcd hda
  · exact hsep2 b d c (hsupp hab).2 (hsupp hda).1 hbd hbc hcd
  · exact hsep1 b c (hsupp hab).2 (hsupp hcd).1 hbc
  · exact hsep1 b c (hsupp hab).2 (hsupp hcd).1 hbc
  · exact hsep2 c a d (hsupp hbc).2 (hsupp hab).1 (Ne.symm hac) hcd hda
  · exact hsep1 c d (hsupp hbc).2 (hsupp hda).1 hcd
  · exact hsep1 d a (hsupp hcd).2 (hsupp hab).1 hda
  · exact hH a b c d hac hbd hab hbc hcd hda

end JSP000838.Gluing
