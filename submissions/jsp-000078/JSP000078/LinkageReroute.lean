import JSP000078.Linkage
import JSP000078.PathSplit

/-!
# Shortening the stem of a two-arm configuration

A connector reaching the stem beyond the branch gives a new branch with a
strictly shorter stem. Erasing detours from the two new arms preserves all
support restrictions.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- Reroute a two-arm configuration at a later vertex of its stem. -/
theorem LinkageY.exists_reroute_shorter (Y : LinkageY G A B) {x y : V}
    (S : Y.SourcePair x) (W : G.Walk S.source y)
    (hy : y ∈ Y.stem.support) (hyne : y ≠ Y.branch)
    (hWV : Disjoint {v | v ∈ W.support} {v | v ∈ S.arm.support})
    (hWS : ∀ v ∈ W.support, v ∈ Y.stem.support → v = y)
    (hWB : ∀ v ∈ W.support, v ∈ B → v = y) :
    ∃ Y' : LinkageY G A B, Y'.stem.length < Y.stem.length := by
  classical
  let pref := Y.stem.takeUntil y hy
  let suff := Y.stem.dropUntil y hy
  let new₁ := W.bypass
  let new₂ := (S.arm.append pref).bypass
  have hpref : pref.support ⊆ Y.stem.support := Y.stem.support_takeUntil_subset_support hy
  have hsuff : suff.support ⊆ Y.stem.support := Y.stem.support_dropUntil_subset_support hy
  have htS : Y.branch ∉ suff.support :=
    path_start_notMem_support_dropUntil Y.pathStem hy hyne
  have htB : Y.branch ∉ B :=
    path_start_notMem_of_end_contact Y.pathStem hy hyne Y.stem_B
  have hnew₁ : new₁.support ⊆ W.support := W.support_bypass_subset_support
  have hnew₂ : new₂.support ⊆ (S.arm.append pref).support :=
    (S.arm.append pref).support_bypass_subset_support
  let Y' : LinkageY G A B := {
    left₁ := S.source
    left₂ := S.other
    branch := y
    right := Y.right
    arm₁ := new₁
    arm₂ := new₂
    stem := suff
    path₁ := W.bypass_isPath
    path₂ := (S.arm.append pref).bypass_isPath
    pathStem := Y.pathStem.dropUntil hy
    left₁_mem := S.source_mem
    left₂_mem := S.other_mem
    left_ne := S.source_ne
    right_mem := Y.right_mem
    arms_inter := by
      intro v hv₁ hv₂
      have hvW := hnew₁ hv₁
      rcases (Walk.mem_support_append_iff S.arm pref).mp (hnew₂ hv₂) with hvV | hvP
      · exact (Set.disjoint_left.mp hWV hvW hvV).elim
      · exact hWS v hvW (hpref hvP)
    arm₁_stem := by
      intro v hv₁ hvS
      exact hWS v (hnew₁ hv₁) (hsuff hvS)
    arm₂_stem := by
      intro v hv₂ hvS
      rcases (Walk.mem_support_append_iff S.arm pref).mp (hnew₂ hv₂) with hvV | hvP
      · have hvt := S.arm_stem v hvV (hsuff hvS)
        exact (htS (hvt ▸ hvS)).elim
      · exact support_intersection_takeUntil_dropUntil Y.pathStem hy v hvP hvS
    arm₁_B := by
      intro v hv₁ hvB
      exact hWB v (hnew₁ hv₁) hvB
    arm₂_B := by
      intro v hv₂ hvB
      rcases (Walk.mem_support_append_iff S.arm pref).mp (hnew₂ hv₂) with hvV | hvP
      · exact (htB (S.arm_B v hvV hvB ▸ hvB)).elim
      · exact path_takeUntil_end_contact Y.pathStem hy Y.stem_B v hvP hvB
    stem_A := by
      intro v hvS hvA
      exact (htS (Y.stem_A v (hsuff hvS) hvA ▸ hvS)).elim
    stem_B := by
      intro v hvS hvB
      exact Y.stem_B v (hsuff hvS) hvB
  }
  exact ⟨Y', Y.stem.length_dropUntil_lt_length hy hyne⟩

end JSP000078
