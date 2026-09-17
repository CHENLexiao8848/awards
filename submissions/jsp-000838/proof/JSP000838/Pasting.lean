import JSP000838.Carrier
import JSP000838.Gluing

namespace JSP000838

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Union of the chosen local graphs, indexed by the actual blocks. -/
def pastedGraph (B : Finset (Finset V)) (F : Finset V → SimpleGraph V) : SimpleGraph V where
  Adj x y := ∃ S ∈ B, (F S).Adj x y
  symm := by
    constructor
    rintro x y ⟨S, hS, hxy⟩
    exact ⟨S, hS, hxy.symm⟩
  loopless := by
    constructor
    rintro x ⟨S, _, hxx⟩
    exact (F S).irrefl hxx

omit [Fintype V] [DecidableEq V] in
theorem pastedGraph_empty (F : Finset V → SimpleGraph V) : pastedGraph ∅ F = ⊥ := by
  ext x y
  simp [pastedGraph]

omit [Fintype V] in
theorem pastedGraph_insert (B : Finset (Finset V)) (S : Finset V)
    (F : Finset V → SimpleGraph V) :
    pastedGraph (insert S B) F = pastedGraph B F ⊔ F S := by
  ext x y
  simp [pastedGraph, or_comm]

omit [Fintype V] in
theorem pastedGraph_adj_shadow {B : Finset (Finset V)} {F : Finset V → SimpleGraph V}
    (hsupp : ∀ S ∈ B, ∀ x y, (F S).Adj x y → x ∈ S ∧ y ∈ S)
    {x y : V} (h : (pastedGraph B F).Adj x y) : y ∈ shadowClosed B x := by
  obtain ⟨S, hS, hxy⟩ := h
  exact mem_shadowClosed.mpr (Or.inr ⟨S, hS, hsupp S hS x y hxy⟩)

omit [Fintype V] in
/-- Gluing locally short-cycle-free graphs along a separated carrier cannot
create triangles or quadrilaterals. -/
theorem SeparatedFamily.pasted_safe {B : Finset (Finset V)} (hB : SeparatedFamily B)
    (F : Finset V → SimpleGraph V)
    (hsupp : ∀ S ∈ B, ∀ x y, (F S).Adj x y → x ∈ S ∧ y ∈ S)
    (hlocal : ∀ S ∈ B, Gluing.TriangleFree (F S) ∧ Gluing.FourCycleFree (F S)) :
    Gluing.TriangleFree (pastedGraph B F) ∧ Gluing.FourCycleFree (pastedGraph B F) := by
  induction hB with
  | empty =>
      rw [pastedGraph_empty]
      constructor <;> simp [Gluing.TriangleFree, Gluing.FourCycleFree]
  | @insert B S hB hcard hnot hsep ih =>
      have hsuppB := fun T hT => hsupp T (mem_insert_of_mem hT)
      have hlocalB := fun T hT => hlocal T (mem_insert_of_mem hT)
      obtain ⟨hG3, hG4⟩ := ih hsuppB hlocalB
      have hsuppS : ∀ ⦃x y⦄, (F S).Adj x y → x ∈ (S : Set V) ∧ y ∈ (S : Set V) :=
        fun {x y} => hsupp S (mem_insert_self S B) x y
      have h1 : ∀ x y, x ∈ (S : Set V) → y ∈ (S : Set V) →
          (pastedGraph B F).Adj x y → False := by
        intro x y hx hy hxy
        apply hsep hx hy hxy.ne
        exact mem_threeStep.mpr ⟨x, shadowClosed_refl B x, x, shadowClosed_refl B x,
          pastedGraph_adj_shadow hsuppB hxy⟩
      have h2 : ∀ x y z, x ∈ (S : Set V) → y ∈ (S : Set V) → x ≠ y →
          (pastedGraph B F).Adj x z → (pastedGraph B F).Adj z y → False := by
        intro x y z hx hy hne hxz hzy
        apply hsep hx hy hne
        exact mem_threeStep.mpr ⟨x, shadowClosed_refl B x, z,
          pastedGraph_adj_shadow hsuppB hxz, pastedGraph_adj_shadow hsuppB hzy⟩
      have h3 : ∀ x y z w, x ∈ (S : Set V) → y ∈ (S : Set V) → x ≠ y →
          (pastedGraph B F).Adj x z → (pastedGraph B F).Adj z w →
          (pastedGraph B F).Adj w y → False := by
        intro x y z w hx hy hne hxz hzw hwy
        apply hsep hx hy hne
        exact mem_threeStep.mpr ⟨z, pastedGraph_adj_shadow hsuppB hxz,
          w, pastedGraph_adj_shadow hsuppB hzw, pastedGraph_adj_shadow hsuppB hwy⟩
      obtain ⟨hS3, hS4⟩ := hlocal S (mem_insert_self S B)
      rw [pastedGraph_insert]
      exact ⟨Gluing.triangleFree_sup _ _ _ hG3 hS3 hsuppS h1 h2,
        Gluing.fourCycleFree_sup _ _ _ hG4 hS4 hsuppS h1 h2 h3⟩

end JSP000838
