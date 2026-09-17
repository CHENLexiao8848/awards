import JSP000078.PathTrimming
import JSP000078.PathGluing

/-!
# A two-arm configuration for the two-link theorem

The arms start in the first vertex set and meet a stem at their common
endpoint. The stem ends in the second set. Shortening the stem by rerouting
will either improve the configuration or produce two disjoint links.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- Two arms into a branch vertex, and a stem from there to the other set. -/
structure LinkageY (G : SimpleGraph V) (A B : Set V) where
  left₁ : V
  left₂ : V
  branch : V
  right : V
  arm₁ : G.Walk left₁ branch
  arm₂ : G.Walk left₂ branch
  stem : G.Walk branch right
  path₁ : arm₁.IsPath
  path₂ : arm₂.IsPath
  pathStem : stem.IsPath
  left₁_mem : left₁ ∈ A
  left₂_mem : left₂ ∈ A
  left_ne : left₁ ≠ left₂
  right_mem : right ∈ B
  arms_inter : ∀ v ∈ arm₁.support, v ∈ arm₂.support → v = branch
  arm₁_stem : ∀ v ∈ arm₁.support, v ∈ stem.support → v = branch
  arm₂_stem : ∀ v ∈ arm₂.support, v ∈ stem.support → v = branch
  arm₁_B : ∀ v ∈ arm₁.support, v ∈ B → v = branch
  arm₂_B : ∀ v ∈ arm₂.support, v ∈ B → v = branch
  stem_A : ∀ v ∈ stem.support, v ∈ A → v = branch
  stem_B : ∀ v ∈ stem.support, v ∈ B → v = right

/-- The left side of the configuration, omitting the branch vertex. -/
def LinkageY.leftRegion (Y : LinkageY G A B) : Set V :=
  {v | (v ∈ A ∨ v ∈ Y.arm₁.support ∨ v ∈ Y.arm₂.support) ∧ v ≠ Y.branch}

/-- The right side of the configuration, omitting the branch vertex. -/
def LinkageY.rightRegion (Y : LinkageY G A B) : Set V :=
  {v | (v ∈ B ∨ v ∈ Y.stem.support) ∧ v ≠ Y.branch}

/-- The normalized support conditions separate the two regions. -/
theorem LinkageY.regions_disjoint (Y : LinkageY G A B) (hAB : Disjoint A B) :
    Disjoint Y.leftRegion Y.rightRegion := by
  apply Set.disjoint_left.mpr
  intro v hvL hvR
  obtain ⟨hvL, hvne⟩ := hvL
  obtain ⟨hvR, _⟩ := hvR
  rcases hvL with hvA | hv₁ | hv₂
  · rcases hvR with hvB | hvS
    · exact Set.disjoint_left.mp hAB hvA hvB
    · exact hvne (Y.stem_A v hvS hvA)
  · rcases hvR with hvB | hvS
    · exact hvne (Y.arm₁_B v hv₁ hvB)
    · exact hvne (Y.arm₁_stem v hv₁ hvS)
  · rcases hvR with hvB | hvS
    · exact hvne (Y.arm₂_B v hv₂ hvB)
    · exact hvne (Y.arm₂_stem v hv₂ hvS)

/-- One arm endpoint survives deletion of the branch. -/
theorem LinkageY.leftRegion_nonempty (Y : LinkageY G A B) :
    Y.leftRegion.Nonempty := by
  by_cases h : Y.left₁ = Y.branch
  · refine ⟨Y.left₂, Or.inl Y.left₂_mem, ?_⟩
    intro h₂
    exact Y.left_ne (h.trans h₂.symm)
  · exact ⟨Y.left₁, Or.inl Y.left₁_mem, h⟩

/-- Exchange the arms without changing the stem or the branch. -/
def LinkageY.swap (Y : LinkageY G A B) : LinkageY G A B where
  left₁ := Y.left₂
  left₂ := Y.left₁
  branch := Y.branch
  right := Y.right
  arm₁ := Y.arm₂
  arm₂ := Y.arm₁
  stem := Y.stem
  path₁ := Y.path₂
  path₂ := Y.path₁
  pathStem := Y.pathStem
  left₁_mem := Y.left₂_mem
  left₂_mem := Y.left₁_mem
  left_ne := Y.left_ne.symm
  right_mem := Y.right_mem
  arms_inter := fun v hv₂ hv₁ ↦ Y.arms_inter v hv₁ hv₂
  arm₁_stem := Y.arm₂_stem
  arm₂_stem := Y.arm₁_stem
  arm₁_B := Y.arm₂_B
  arm₂_B := Y.arm₁_B
  stem_A := Y.stem_A
  stem_B := Y.stem_B

/-- The source path chosen on the left and the unused arm have disjoint supports. -/
structure LinkageY.SourcePair (Y : LinkageY G A B) (x : V) where
  source : V
  other : V
  front : G.Walk source x
  arm : G.Walk other Y.branch
  source_mem : source ∈ A
  other_mem : other ∈ A
  source_ne : source ≠ other
  prefix_left : ∀ v ∈ front.support, v ∈ Y.leftRegion
  prefix_arm : Disjoint {v | v ∈ front.support} {v | v ∈ arm.support}
  prefix_stem : Disjoint {v | v ∈ front.support} {v | v ∈ Y.stem.support}
  arm_left : ∀ v ∈ arm.support, v = Y.branch ∨ v ∈ Y.leftRegion
  arm_stem : ∀ v ∈ arm.support, v ∈ Y.stem.support → v = Y.branch
  arm_B : ∀ v ∈ arm.support, v ∈ B → v = Y.branch
  arm_path : arm.IsPath

/-- If a connector starts on the first arm, use its prefix and retain the second arm. -/
noncomputable def LinkageY.sourcePair_of_mem_arm₁ (Y : LinkageY G A B)
    {x : V} (hx : x ∈ Y.arm₁.support) (hxne : x ≠ Y.branch) : Y.SourcePair x := by
  classical
  let p := Y.arm₁.takeUntil x hx
  have hpSub : p.support ⊆ Y.arm₁.support := Y.arm₁.support_takeUntil_subset_support hx
  have ht : Y.branch ∉ p.support :=
    Walk.endpoint_notMem_support_takeUntil Y.path₁ hx hxne.symm
  refine ⟨Y.left₁, Y.left₂, p, Y.arm₂, Y.left₁_mem, Y.left₂_mem,
    Y.left_ne, ?_, ?_, ?_, ?_, Y.arm₂_stem, Y.arm₂_B, Y.path₂⟩
  · intro v hv
    exact ⟨Or.inr (Or.inl (hpSub hv)), fun h ↦ ht (h ▸ hv)⟩
  · apply Set.disjoint_left.mpr
    intro v hv h₂
    exact ht (Y.arms_inter v (hpSub hv) h₂ ▸ hv)
  · apply Set.disjoint_left.mpr
    intro v hv hS
    exact ht (Y.arm₁_stem v (hpSub hv) hS ▸ hv)
  · intro v hv
    by_cases ht : v = Y.branch
    · exact Or.inl ht
    · exact Or.inr ⟨Or.inr (Or.inr hv), ht⟩

@[simp]
theorem LinkageY.leftRegion_swap (Y : LinkageY G A B) :
    Y.swap.leftRegion = Y.leftRegion := by
  ext v
  simp only [leftRegion, swap, Set.mem_ofPred_eq]
  tauto

/-- Choose the used prefix and an unused arm from any point of the left region. -/
noncomputable def LinkageY.sourcePair (Y : LinkageY G A B)
    {x : V} (hx : x ∈ Y.leftRegion) : Y.SourcePair x := by
  classical
  by_cases h₁ : x ∈ Y.arm₁.support
  · exact Y.sourcePair_of_mem_arm₁ h₁ hx.2
  by_cases h₂ : x ∈ Y.arm₂.support
  · let S := Y.swap.sourcePair_of_mem_arm₁ h₂ hx.2
    refine ⟨S.source, S.other, S.front, S.arm, S.source_mem, S.other_mem,
      S.source_ne, ?_, S.prefix_arm, S.prefix_stem, ?_, S.arm_stem, S.arm_B, S.arm_path⟩
    · intro v hv
      simpa only [leftRegion_swap] using S.prefix_left v hv
    · intro v hv
      change v = Y.swap.branch ∨ v ∈ Y.leftRegion
      simpa only [leftRegion_swap] using S.arm_left v hv
  · have hxA : x ∈ A := hx.1.resolve_right (by tauto)
    have hxne : x ≠ Y.left₁ := fun h ↦ h₁ (h ▸ Y.arm₁.start_mem_support)
    refine ⟨x, Y.left₁, Walk.nil, Y.arm₁, hxA, Y.left₁_mem, hxne,
      ?_, ?_, ?_, ?_, Y.arm₁_stem, Y.arm₁_B, Y.path₁⟩
    · intro v hv
      have hvx : v = x := by simpa using hv
      exact hvx ▸ hx
    · apply Set.disjoint_left.mpr
      intro v hv hV
      have hvx : v = x := by simpa using hv
      exact h₁ (hvx ▸ hV)
    · apply Set.disjoint_left.mpr
      intro v hv hS
      have hvx : v = x := by simpa using hv
      exact hx.2 (Y.stem_A x (hvx ▸ hS) hxA)
    · intro v hv
      by_cases ht : v = Y.branch
      · exact Or.inl ht
      · exact Or.inr ⟨Or.inr (Or.inl hv), ht⟩

end JSP000078
