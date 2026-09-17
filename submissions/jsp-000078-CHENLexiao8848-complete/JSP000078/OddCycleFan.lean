import JSP000078.CycleChords
import JSP000078.MathlibBridge

/-!
# The odd-cycle case of Gyárfás's Lemma 2

Each incident chord of an odd cycle makes one shorter odd cycle. Divide the
chords according to which arc supplies that odd cycle. Within either class
the lengths are distinct, so one class supplies at least half the chords.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The even chord positions give different shorter odd cycles along the forward arc. -/
theorem card_even_cycle_chords_le_shorter_odd_lengths {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (J : Finset (Fin C.length))
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) :
    (J.filter fun j ↦ Even j.val).card ≤
      ((oddCycleLengths G).filter fun n ↦ n < C.length).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun j : Fin C.length ↦ j.val + 1)
  · intro j hj
    obtain ⟨hjJ, hjEven⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj2, hjend, hjAdj⟩ := hJ j hjJ
    obtain ⟨E, F, hE, _, hlen, _⟩ := exists_cycles_of_cycle_getVert_adj hC hj2 hjend hjAdj
    apply Finset.mem_filter.mpr
    refine ⟨(mem_oddCycleLengths G).mpr ⟨?_, c, E, hE, hlen⟩, ?_⟩
    · exact hjEven.add_odd odd_one
    · change j.val + 1 < C.length
      omega
  · intro i _ j _ hij
    apply Fin.ext
    change i.val + 1 = j.val + 1 at hij
    omega

/-- The odd chord positions give different shorter odd cycles along the other arc. -/
theorem card_odd_cycle_chords_le_shorter_odd_lengths {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (J : Finset (Fin C.length))
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) :
    (J.filter fun j ↦ ¬ Even j.val).card ≤
      ((oddCycleLengths G).filter fun n ↦ n < C.length).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun j : Fin C.length ↦ C.length - j.val + 1)
  · intro j hj
    obtain ⟨hjJ, hjOdd⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj2, hjend, hjAdj⟩ := hJ j hjJ
    obtain ⟨E, F, _, hF, _, hlen⟩ := exists_cycles_of_cycle_getVert_adj hC hj2 hjend hjAdj
    apply Finset.mem_filter.mpr
    refine ⟨(mem_oddCycleLengths G).mpr ⟨?_, c, F, hF, hlen⟩, ?_⟩
    · have hjO : Odd j.val := Nat.not_even_iff_odd.mp hjOdd
      simp only [Nat.odd_iff] at hCO hjO ⊢
      omega
    · change C.length - j.val + 1 < C.length
      omega
  · intro i hi j hj hij
    apply Fin.ext
    change C.length - i.val + 1 = C.length - j.val + 1 at hij
    have hiL := i.isLt
    have hjL := j.isLt
    omega

/-- Gyárfás Lemma 2 when the underlying cycle is odd, retaining the stronger
fact that the produced odd lengths are all shorter than that cycle. -/
theorem odd_cycle_many_chords_shorter_lengths {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (k : ℕ) (hk : 1 ≤ k)
    (J : Finset (Fin C.length)) (hcard : 2 * k - 1 ≤ J.card)
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val)) :
    k ≤ ((oddCycleLengths G).filter fun n ↦ n < C.length).card := by
  classical
  have hEven := card_even_cycle_chords_le_shorter_odd_lengths hC J hJ
  have hOdd := card_odd_cycle_chords_le_shorter_odd_lengths hC hCO J hJ
  have hsum := Finset.card_filter_add_card_filter_not (s := J) (fun j ↦ Even j.val)
  omega

end JSP000078
