import JSP000078.CycleArcs
import Mathlib.Algebra.Ring.Parity

/-!
# Splicing disjoint odd cycles along two links

The length calculation in Gyárfás's Lemma 1 uses two odd cycles assembled
from complementary arcs and two clean disjoint links. Their combined
length is the sum of the original lengths plus twice the linking lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two arcs in disjoint sets and two clean disjoint linking paths form a
simple cycle. The displayed walk fixes the orientation for length sums. -/
theorem isCycle_splice_paths_between_sets {A B : Set V} {a₁ a₂ b₁ b₂ : V}
    {U : G.Walk a₁ a₂} {V' : G.Walk b₁ b₂}
    {p : G.Walk a₁ b₁} {q : G.Walk a₂ b₂}
    (hAB : Disjoint A B) (hU : U.IsPath) (hV : V'.IsPath)
    (hp : p.IsPath) (hq : q.IsPath)
    (hUA : ∀ x ∈ U.support, x ∈ A) (hVB : ∀ x ∈ V'.support, x ∈ B)
    (hpq : Disjoint {x | x ∈ p.support} {x | x ∈ q.support})
    (hpA : ∀ x ∈ p.support, x ∈ A → x = a₁)
    (hqA : ∀ x ∈ q.support, x ∈ A → x = a₂)
    (hpB : ∀ x ∈ p.support, x ∈ B → x = b₁)
    (hqB : ∀ x ∈ q.support, x ∈ B → x = b₂)
    (hlen : 3 ≤ U.length + q.length + V'.length + p.length) :
    ((U.append q).append (V'.reverse.append p.reverse)).IsCycle := by
  apply isCycle_append_four_of_support_intersections hU hq hV.reverse hp.reverse
  · intro x hxU hxq
    exact hqA x hxq (hUA x hxU)
  · intro x hxq hxV
    have hxV' : x ∈ V'.support := by simpa using hxV
    exact hqB x hxq (hVB x hxV')
  · intro x hxV hxp
    have hxV' : x ∈ V'.support := by simpa using hxV
    have hxp' : x ∈ p.support := by simpa using hxp
    exact hpB x hxp' (hVB x hxV')
  · intro x hxp hxU
    exact hpA x (by simpa using hxp) (hUA x hxU)
  · apply Set.disjoint_left.mpr
    intro x hxU hxV
    exact Set.disjoint_left.mp hAB (hUA x hxU) (hVB x (by simpa using hxV))
  · apply Set.disjoint_left.mpr
    intro x hxq hxp
    exact Set.disjoint_left.mp hpq (by simpa using hxp) hxq
  · simpa only [Walk.length_reverse] using hlen

/-- Complementary pieces of two odd lengths can be paired so that both
paired sums, after adding a fixed linking length, are odd. -/
theorem odd_complementary_length_pairing {a b c d t : ℕ}
    (hab : Odd (a + b)) (hcd : Odd (c + d)) :
    (Odd (a + c + t) ∧ Odd (b + d + t)) ∨
      (Odd (a + d + t) ∧ Odd (b + c + t)) := by
  simp only [Nat.odd_iff] at *
  omega

/-- Two disjoint odd cycles and two clean vertex-disjoint links produce
two odd cycles whose total length includes both original cycles and both
links twice. This is the cycle-splicing calculation in Gyárfás's Lemma 1. -/
theorem exists_two_odd_cycles_of_two_links {c d a₁ a₂ b₁ b₂ : V}
    {C : G.Walk c c} {D : G.Walk d d}
    (hC : C.IsCycle) (hD : D.IsCycle) (hCO : Odd C.length) (hDO : Odd D.length)
    (hCD : Disjoint {x | x ∈ C.support} {x | x ∈ D.support})
    {p : G.Walk a₁ b₁} {q : G.Walk a₂ b₂} (hp : p.IsPath) (hq : q.IsPath)
    (ha₁ : a₁ ∈ C.support) (ha₂ : a₂ ∈ C.support)
    (hb₁ : b₁ ∈ D.support) (hb₂ : b₂ ∈ D.support)
    (hpq : Disjoint {x | x ∈ p.support} {x | x ∈ q.support})
    (hpC : ∀ x ∈ p.support, x ∈ C.support → x = a₁)
    (hqC : ∀ x ∈ q.support, x ∈ C.support → x = a₂)
    (hpD : ∀ x ∈ p.support, x ∈ D.support → x = b₁)
    (hqD : ∀ x ∈ q.support, x ∈ D.support → x = b₂) :
    ∃ E F : G.Walk a₁ a₁, E.IsCycle ∧ F.IsCycle ∧ Odd E.length ∧ Odd F.length ∧
      E.length + F.length = C.length + D.length + 2 * (p.length + q.length) := by
  have haa : a₁ ≠ a₂ := by
    intro h
    exact Set.disjoint_left.mp hpq p.start_mem_support (h ▸ q.start_mem_support)
  have hbb : b₁ ≠ b₂ := by
    intro h
    exact Set.disjoint_left.mp hpq p.end_mem_support (h ▸ q.end_mem_support)
  have hab₁ : a₁ ≠ b₁ := by
    intro h
    exact Set.disjoint_left.mp hCD ha₁ (h ▸ hb₁)
  have hpPos : 0 < p.length := Nat.pos_of_ne_zero fun h ↦ hab₁ (Walk.eq_of_length_eq_zero h)
  obtain ⟨U₁, U₂, hU₁, hU₂, hU₁C, hU₂C, _, hUC⟩ :=
    exists_cycle_arcs hC ha₁ ha₂ haa
  obtain ⟨V₁, V₂, hV₁, hV₂, hV₁D, hV₂D, _, hVD⟩ :=
    exists_cycle_arcs hD hb₁ hb₂ hbb
  have hU₁Pos : 0 < U₁.length := Nat.pos_of_ne_zero fun h ↦ haa (Walk.eq_of_length_eq_zero h)
  have hU₂Pos : 0 < U₂.length := Nat.pos_of_ne_zero fun h ↦ haa (Walk.eq_of_length_eq_zero h)
  have hV₁Pos : 0 < V₁.length := Nat.pos_of_ne_zero fun h ↦ hbb (Walk.eq_of_length_eq_zero h)
  have hV₂Pos : 0 < V₂.length := Nat.pos_of_ne_zero fun h ↦ hbb (Walk.eq_of_length_eq_zero h)
  let splice (U : G.Walk a₁ a₂) (V' : G.Walk b₁ b₂) : G.Walk a₁ a₁ :=
    (U.append q).append (V'.reverse.append p.reverse)
  have hlen (U : G.Walk a₁ a₂) (V' : G.Walk b₁ b₂) :
      (splice U V').length = U.length + V'.length + (p.length + q.length) := by
    simp only [splice, Walk.length_append, Walk.length_reverse]
    omega
  have hcycle (U : G.Walk a₁ a₂) (V' : G.Walk b₁ b₂)
      (hU : U.IsPath) (hV : V'.IsPath)
      (hUC' : ∀ x ∈ U.support, x ∈ C.support)
      (hVD' : ∀ x ∈ V'.support, x ∈ D.support)
      (hUPos : 0 < U.length) (hVPos : 0 < V'.length) : (splice U V').IsCycle := by
    exact isCycle_splice_paths_between_sets hCD hU hV hp hq hUC' hVD' hpq
      hpC hqC hpD hqD (by omega)
  have hUOdd : Odd (U₁.length + U₂.length) := hUC.symm ▸ hCO
  have hVOdd : Odd (V₁.length + V₂.length) := hVD.symm ▸ hDO
  rcases odd_complementary_length_pairing (t := p.length + q.length) hUOdd hVOdd with h | h
  · refine ⟨splice U₁ V₁, splice U₂ V₂,
      hcycle U₁ V₁ hU₁ hV₁ hU₁C hV₁D hU₁Pos hV₁Pos,
      hcycle U₂ V₂ hU₂ hV₂ hU₂C hV₂D hU₂Pos hV₂Pos, ?_, ?_, ?_⟩
    · simpa only [hlen] using h.1
    · simpa only [hlen] using h.2
    · rw [hlen, hlen]
      omega
  · refine ⟨splice U₁ V₂, splice U₂ V₁,
      hcycle U₁ V₂ hU₁ hV₂ hU₁C hV₂D hU₁Pos hV₂Pos,
      hcycle U₂ V₁ hU₂ hV₁ hU₂C hV₁D hU₂Pos hV₁Pos, ?_, ?_, ?_⟩
    · simpa only [hlen] using h.1
    · simpa only [hlen] using h.2
    · rw [hlen, hlen]
      omega

end JSP000078
