import JSP000078.Linkage
import JSP000078.CycleLinking

/-! # A connector across the two sides of a normalized Y -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- Delete the branch and trim a surviving path between the two regions. -/
theorem LinkageY.exists_connector [Fintype V] (Y : LinkageY G A B)
    (hG : TwoVertexConnected G) (hB : ∃ b ∈ B, b ≠ Y.branch) :
    ∃ (x y : V) (q : G.Walk x y),
      x ∈ Y.leftRegion ∧ y ∈ Y.rightRegion ∧ q.IsPath ∧ Y.branch ∉ q.support ∧
      (∀ v ∈ q.support, v ∈ Y.leftRegion → v = x) ∧
      (∀ v ∈ q.support, v ∈ Y.rightRegion → v = y) := by
  obtain ⟨a, ha⟩ := Y.leftRegion_nonempty
  obtain ⟨b, hb, hbne⟩ := hB
  have hbR : b ∈ Y.rightRegion := ⟨Or.inl hb, hbne⟩
  obtain ⟨p, hp, ht⟩ := exists_path_avoiding_vertex hG Y.branch a b ha.2 hbne
  obtain ⟨x, y, q, hq, hx, hy, hsub, hL, hR⟩ :=
    exists_trimmed_path_between_sets p hp ha hbR
  exact ⟨x, y, q, hx, hy, hq, fun h ↦ ht (hsub h), hL, hR⟩

/-- Combining the chosen left prefix with the connector gives exactly the
support conditions needed for rerouting or extracting disjoint links. -/
theorem LinkageY.connector_supports (Y : LinkageY G A B) (hAB : Disjoint A B)
    {x y : V} (S : Y.SourcePair x) (q : G.Walk x y)
    (ht : Y.branch ∉ q.support)
    (hL : ∀ v ∈ q.support, v ∈ Y.leftRegion → v = x)
    (hR : ∀ v ∈ q.support, v ∈ Y.rightRegion → v = y) :
    Disjoint {v | v ∈ (S.front.append q).support} {v | v ∈ S.arm.support} ∧
    (∀ v ∈ (S.front.append q).support, v ∈ Y.stem.support → v = y) ∧
    (∀ v ∈ (S.front.append q).support, v ∈ B → v = y) := by
  have hxV : x ∉ S.arm.support := fun hv ↦
    Set.disjoint_left.mp S.prefix_arm S.front.end_mem_support hv
  have hqne : ∀ v ∈ q.support, v ≠ Y.branch := fun v hv heq ↦ ht (heq ▸ hv)
  refine ⟨?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro v hv hV
    rcases (Walk.mem_support_append_iff S.front q).mp hv with hp | hq
    · exact Set.disjoint_left.mp S.prefix_arm hp hV
    · rcases S.arm_left v hV with heq | hleft
      · exact hqne v hq heq
      · exact hxV (hL v hq hleft ▸ hV)
  · intro v hv hStem
    rcases (Walk.mem_support_append_iff S.front q).mp hv with hp | hq
    · exact (Set.disjoint_left.mp S.prefix_stem hp hStem).elim
    · exact hR v hq ⟨Or.inr hStem, hqne v hq⟩
  · intro v hv hB
    rcases (Walk.mem_support_append_iff S.front q).mp hv with hp | hq
    · have hleft := S.prefix_left v hp
      exact (Set.disjoint_left.mp (Y.regions_disjoint hAB) hleft
        ⟨Or.inl hB, hleft.2⟩).elim
    · exact hR v hq ⟨Or.inl hB, hqne v hq⟩

/-- Two walks between the sets with disjoint supports can both be simplified
and trimmed while keeping the disjointness and exact endpoint contacts. -/
theorem exists_trimmed_disjoint_links {a₁ a₂ b₁ b₂ : V}
    (p : G.Walk a₁ b₁) (q : G.Walk a₂ b₂)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hdis : Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) :
    ∃ (a₁ a₂ b₁ b₂ : V) (P₁ : G.Walk a₁ b₁) (P₂ : G.Walk a₂ b₂),
      P₁.IsPath ∧ P₂.IsPath ∧ a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
      Disjoint {v | v ∈ P₁.support} {v | v ∈ P₂.support} ∧
      (∀ v ∈ P₁.support, v ∈ A → v = a₁) ∧
      (∀ v ∈ P₂.support, v ∈ A → v = a₂) ∧
      (∀ v ∈ P₁.support, v ∈ B → v = b₁) ∧
      (∀ v ∈ P₂.support, v ∈ B → v = b₂) := by
  obtain ⟨a₁', b₁', p', hp', ha₁', hb₁', hsub₁, hA₁, hB₁⟩ :=
    exists_trimmed_path_of_walk_between_sets p ha₁ hb₁
  obtain ⟨a₂', b₂', q', hq', ha₂', hb₂', hsub₂, hA₂, hB₂⟩ :=
    exists_trimmed_path_of_walk_between_sets q ha₂ hb₂
  refine ⟨a₁', a₂', b₁', b₂', p', q', hp', hq', ha₁', ha₂', hb₁', hb₂',
    ?_, hA₁, hA₂, hB₁, hB₂⟩
  exact Set.disjoint_left.mpr fun v hp hq ↦ Set.disjoint_left.mp hdis (hsub₁ hp) (hsub₂ hq)

end JSP000078
