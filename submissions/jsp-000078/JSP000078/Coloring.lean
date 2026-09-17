import JSP000078.OddCycles
import JSP000078.Parity
import JSP000078.DepthFirst

/-!
# Coloring a depth-first stack

Each of the two alternating parity classes has a palette of `k + 1`
colors. Distinct forbidden positions produce distinct odd cycle lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- There is a color extending any simple stack with alternating first
coordinates, avoiding all previously colored neighbors in that stack. -/
theorem exists_stack_color (k : ℕ) (hk : (oddCycleLengths G).card ≤ k)
    (l : List V) (x : V) (f : V → Bool × Fin (k + 1))
    (hnd : (x :: l).Nodup) (hgraph : (x :: l).IsChain G.Adj)
    (hcolor : (l.map f).IsChain (fun a b => a.1 ≠ b.1)) :
    ∃ c : Bool × Fin (k + 1),
      (c :: l.map f).IsChain (fun a b => a.1 ≠ b.1) ∧
      ∀ y ∈ l, G.Adj x y → c ≠ f y := by
  classical
  cases l with
  | nil =>
      exact ⟨(false, 0), by simp, by simp⟩
  | cons v l =>
      let s := v :: l
      let b := !(f v).1
      let I := oddStackNeighborIndices G x s
      let forbidden : Finset (Fin (k + 1)) := I.image fun i => (f s[i.val]).2
      have hI : I.card ≤ (oddCycleLengths G).card :=
        card_oddStackNeighborIndices_le x s hnd hgraph
      have hforbidden : forbidden.card ≤ k :=
        (Finset.card_image_le).trans (hI.trans hk)
      have hlt : forbidden.card < (Finset.univ : Finset (Fin (k + 1))).card := by
        simpa using Nat.lt_succ_of_le hforbidden
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨(b, a), ?_, ?_⟩
      · exact List.isChain_cons_cons.mpr ⟨by simp [b], hcolor⟩
      · intro y hy hxy heq
        have hb : (f y).1 = b := (congrArg Prod.fst heq).symm
        have ha' : (f y).2 = a := (congrArg Prod.snd heq).symm
        obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
        have hchain : s.IsChain (fun u v => (f u).1 ≠ (f v).1) :=
          (List.isChain_map f).mp hcolor
        have hparity : (f s[i]).1 ≠ (f (s.head (by simp [s]))).1 := by
          simp [s, hiy, hb, b]
        have hodd : Odd i :=
          odd_index_of_alternating (fun u => (f u).1) hchain
            (by simp [s]) ⟨i, hi⟩ hparity
        have hiI : (⟨i, hi⟩ : Fin s.length) ∈ I := by
          apply (mem_oddStackNeighborIndices x s ⟨i, hi⟩).mpr
          exact ⟨hodd, by simpa [s, hiy] using hxy⟩
        apply ha
        exact Finset.mem_image.mpr
          ⟨⟨i, hi⟩, hiI, by simpa [s, hiy] using ha'⟩

end JSP000078
