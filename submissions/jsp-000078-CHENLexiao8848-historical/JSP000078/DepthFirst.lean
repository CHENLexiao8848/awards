import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.List.Chain

/-!
# A finite depth-first coloring principle

A local rule which extends a coloring along a simple path produces a coloring
of the whole finite graph. The proof keeps an uncolored set and a path stack.
Its strictly decreasing measure is twice the uncolored cardinality plus the
stack length. No tree or traversal algorithm is assumed.
-/

namespace JSP000078

open SimpleGraph

universe u v

/-- A path-extension rule is sufficient to color a finite graph.

The stack is listed with its newest vertex first. The arbitrary relation R
records the extra condition required between successive stack colors.
-/
theorem coloring_of_path_extension
    {V : Type u} {C : Type v} [Fintype V] [Nonempty C]
    (G : SimpleGraph V) (R : C → C → Prop)
    (extend : ∀ (l : List V) (x : V) (f : V → C),
      (x :: l).Nodup → (x :: l).IsChain G.Adj → (l.map f).IsChain R →
      ∃ c : C, (c :: l.map f).IsChain R ∧
        ∀ y ∈ l, G.Adj x y → c ≠ f y) :
    Nonempty (G.Coloring C) := by
  classical
  have finish : ∀ n : ℕ, ∀ (s : Finset V) (l : List V) (f : V → C),
      2 * s.card + l.length = n →
      l.Nodup → l.IsChain G.Adj → (l.map f).IsChain R →
      (∀ x ∈ l, x ∉ s) →
      (∀ x y, x ∉ s → y ∉ s → G.Adj x y → f x ≠ f y) →
      (∀ x y, x ∈ s → y ∉ s → G.Adj x y → y ∈ l) →
      Nonempty (G.Coloring C) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s l f hn hl hg hc hdis hproper hboundary
      by_cases hs : s.Nonempty
      · by_cases hpush : ∃ x ∈ s, (x :: l).IsChain G.Adj
        · obtain ⟨x, hxs, hchain⟩ := hpush
          have hxl : x ∉ l := fun h => hdis x h hxs
          obtain ⟨c, hcc, havoid⟩ := extend l x f
            (List.nodup_cons.mpr ⟨hxl, hl⟩) hchain hc
          let f' : V → C := fun y => if y = x then c else f y
          have hfx : f' x = c := by simp [f']
          have hfold : ∀ y, y ≠ x → f' y = f y := by
            intro y hy
            simp [f', hy]
          have hmap : l.map f' = l.map f := by
            apply List.map_congr_left
            intro y hy
            exact hfold y (fun h => hxl (h ▸ hy))
          have hcard : (s.erase x).card + 1 = s.card :=
            Finset.card_erase_add_one hxs
          have hlt : 2 * (s.erase x).card + (x :: l).length < n := by
            simp only [List.length_cons]
            omega
          apply ih _ hlt (s.erase x) (x :: l) f' rfl
          · exact List.nodup_cons.mpr ⟨hxl, hl⟩
          · exact hchain
          · simpa only [List.map_cons, hfx, hmap] using hcc
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact Finset.notMem_erase _ s
            · exact fun h => hdis y hy (Finset.mem_of_mem_erase h)
          · intro a b ha hb hab
            by_cases hax : a = x
            · subst a
              have hbx : b ≠ x := hab.ne.symm
              have hbs : b ∉ s := by simpa [Finset.mem_erase, hbx] using hb
              rw [hfx, hfold b hbx]
              exact havoid b (hboundary x b hxs hbs hab) hab
            · by_cases hbx : b = x
              · subst b
                have has : a ∉ s := by simpa [Finset.mem_erase, hax] using ha
                rw [hfold a hax, hfx]
                exact (havoid a (hboundary x a hxs has hab.symm) hab.symm).symm
              · have has : a ∉ s := by simpa [Finset.mem_erase, hax] using ha
                have hbs : b ∉ s := by simpa [Finset.mem_erase, hbx] using hb
                rw [hfold a hax, hfold b hbx]
                exact hproper a b has hbs hab
          · intro a b ha hb hab
            by_cases hbx : b = x
            · simp [hbx]
            · have hbs : b ∉ s := by simpa [Finset.mem_erase, hbx] using hb
              exact List.mem_cons_of_mem x
                (hboundary a b (Finset.mem_of_mem_erase ha) hbs hab)
        · cases l with
          | nil =>
            obtain ⟨x, hx⟩ := hs
            exact (hpush ⟨x, hx, List.isChain_singleton x⟩).elim
          | cons z l =>
            have hlt : 2 * s.card + l.length < n := by
              simp only [List.length_cons] at hn
              omega
            apply ih _ hlt s l f rfl
            · exact (List.nodup_cons.mp hl).2
            · exact hg.tail
            · exact hc.tail
            · intro x hx
              exact hdis x (List.mem_cons_of_mem z hx)
            · exact hproper
            · intro x y hx hy hxy
              have hymem := hboundary x y hx hy hxy
              rcases List.mem_cons.mp hymem with hyz | hyl
              · subst y
                exact (hpush ⟨x, hx, List.isChain_cons_cons.mpr ⟨hxy, hg⟩⟩).elim
              · exact hyl
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        exact ⟨Coloring.mk f (fun h => hproper _ _ (by simp) (by simp) h)⟩
  apply finish _ Finset.univ [] (fun _ => Classical.choice inferInstance) rfl
  · exact List.nodup_nil
  · exact List.isChain_nil
  · exact List.isChain_nil
  · simp
  · simp
  · simp

end JSP000078
