import JSP000838.Pasting
import JSP000838.LocalCycle
import JSP000838.FiniteChoice
import JSP000838.OrderedObstruction
import JSP000838.CoverObstruction
import JSP000838.Cycles
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort

namespace JSP000838

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Sort a five-element block according to an arbitrary ranking of all vertices. -/
theorem exists_sorted_block (S : Finset V) (hS : S.card = 5)
    (r : V ≃ Fin (Fintype.card V)) :
    ∃ e : Fin 5 ≃ S, StrictMono (fun i => r (e i : V)) := by
  let : LinearOrder V := LinearOrder.lift' r r.injective
  exact ⟨(S.orderIsoOfFin hS).toEquiv, (S.orderEmbOfFin hS).strictMono⟩

/-- The finite ordered-template count specialized to separated five-element
blocks. Only elementary finite cardinality is used. -/
theorem exists_ordered_graph_of_carrier (B : Finset (Finset V)) (hB : SeparatedFamily B)
    (hcount : Fintype.card V ^ Fintype.card V * 119 ^ B.card < 120 ^ B.card) :
    ∃ G : SimpleGraph V, NoShortCycles 5 G ∧ HasOrderedFiveCycle G := by
  classical
  let base (S : B) : Fin 5 ≃ (S.val : Finset V) :=
    (Finset.equivFinOfCardEq (hB.card_blocks S.val S.property)).symm
  choose sorted hsorted using fun (r : V ≃ Fin (Fintype.card V)) (S : B) =>
    exists_sorted_block S.val (hB.card_blocks S.val S.property) r
  let required (r : V ≃ Fin (Fintype.card V)) (S : B) : Equiv.Perm (Fin 5) :=
    (sorted r S).trans (base S).symm
  have horders : Fintype.card (V ≃ Fin (Fintype.card V)) ≤
      Fintype.card V ^ Fintype.card V := by
    simpa using Fintype.card_le_of_injective
      (fun r : V ≃ Fin (Fintype.card V) => (r : V → Fin (Fintype.card V)))
      Equiv.coe_fn_injective
  have hchoices : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    decide
  have hbound : Fintype.card (V ≃ Fin (Fintype.card V)) *
      (Fintype.card (Equiv.Perm (Fin 5)) - 1) ^ Fintype.card B <
      Fintype.card (Equiv.Perm (Fin 5)) ^ Fintype.card B := by
    rw [hchoices, Fintype.card_coe]
    norm_num only at *
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ horders) hcount
  obtain ⟨labels, hlabels⟩ := exists_assignment_hits_all required hbound
  let chosen (S : B) : Fin 5 ≃ (S.val : Finset V) := (labels S).trans (base S)
  let F (S : Finset V) : SimpleGraph V :=
    if hS : S ∈ B then LocalCycle.graph (chosen ⟨S, hS⟩) else ⊥
  have hF (S : B) : F S.val = LocalCycle.graph (chosen S) := by simp [F]
  have hsupp : ∀ S ∈ B, ∀ x y, (F S).Adj x y → x ∈ S ∧ y ∈ S := by
    intro S hS x y hxy
    rw [hF ⟨S, hS⟩] at hxy
    exact LocalCycle.supported _ hxy
  have hlocal : ∀ S ∈ B, Gluing.TriangleFree (F S) ∧ Gluing.FourCycleFree (F S) := by
    intro S hS
    rw [hF ⟨S, hS⟩]
    exact ⟨LocalCycle.triangleFree _, LocalCycle.fourCycleFree _⟩
  have hsafe := hB.pasted_safe F hsupp hlocal
  refine ⟨pastedGraph B F, noShortCycles_of_triangleFree_fourCycleFree hsafe.1 hsafe.2, ?_⟩
  intro r
  obtain ⟨S, hS⟩ := hlabels r
  have heq : chosen S = sorted r S := by
    ext i
    simp [chosen, hS, required]
  refine ⟨fun i => (chosen S i : V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [heq, Function.comp_def] using hsorted r S
  all_goals
    refine ⟨S.val, S.property, ?_⟩
    rw [hF S]
  · exact LocalCycle.adj01 _
  · exact LocalCycle.adj12 _
  · exact LocalCycle.adj23 _
  · exact LocalCycle.adj34 _
  · exact LocalCycle.adj04 _

/-- A finite instance of Nešetřil–Rödl's ordered-cycle phenomenon, proved by
an explicit greedy carrier and a finite counting argument. -/
theorem exists_noShortCycles_ordered_five :
    ∃ G : SimpleGraph (Fin carrierN), NoShortCycles 5 G ∧ HasOrderedFiveCycle G := by
  obtain ⟨B, hcard, hB⟩ := exists_large_separated_family
  apply exists_ordered_graph_of_carrier B hB
  apply choice_count_bound_parameters
  · exact Fintype.card_fin _
  · calc
      B.card = carrierM := hcard
      _ = 120 * 96 * Fintype.card (Fin carrierN) := by rw [Fintype.card_fin]

/-- The s=5 non-cover consequence of Nešetřil–Rödl's construction. -/
theorem exists_noShortCycles_not_cover :
    ∃ G : SimpleGraph (Fin carrierN), NoShortCycles 5 G ∧ ¬ IsCoverGraph G := by
  obtain ⟨G, hcycles, hordered⟩ := exists_noShortCycles_ordered_five
  exact ⟨G, hcycles, hordered.not_isCoverGraph⟩

/-- Corollary 4's subgraph formulation at the threshold needed for JSP. -/
theorem exists_noShortCycles_not_hasse_subgraph :
    ∃ G : SimpleGraph (Fin carrierN), NoShortCycles 5 G ∧
      ∀ (W : Type) (P : PartialOrder W),
        ¬ SimpleGraph.IsContained G (@SimpleGraph.hasse W P.toPreorder) := by
  obtain ⟨G, hcycles, hordered⟩ := exists_noShortCycles_ordered_five
  exact ⟨G, hcycles, fun W P => @HasOrderedFiveCycle.not_hasse_subgraph
    (Fin carrierN) _ G hordered W P⟩

end JSP000838
