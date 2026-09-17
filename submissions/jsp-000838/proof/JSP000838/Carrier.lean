import JSP000838.FiniteSeparation
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace JSP000838

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of blocks containing a vertex. -/
def blockLoad (B : Finset (Finset V)) (v : V) : ℕ :=
  (B.filter fun S => v ∈ S).card

/-- A closed neighborhood in the shadow of a family of blocks. -/
def shadowClosed (B : Finset (Finset V)) (v : V) : Finset V :=
  insert v ((B.filter fun S => v ∈ S).biUnion id)

omit [Fintype V] in
theorem mem_shadowClosed {B : Finset (Finset V)} {x y : V} :
    y ∈ shadowClosed B x ↔ y = x ∨ ∃ S ∈ B, x ∈ S ∧ y ∈ S := by
  simp [shadowClosed, and_assoc]

omit [Fintype V] in
theorem shadowClosed_refl (B : Finset (Finset V)) (x : V) :
    x ∈ shadowClosed B x := by simp [shadowClosed]

omit [Fintype V] in
theorem shadowClosed_symm (B : Finset (Finset V)) (x y : V)
    (h : y ∈ shadowClosed B x) : x ∈ shadowClosed B y := by
  rcases mem_shadowClosed.mp h with rfl | ⟨S, hS, hx, hy⟩
  · exact shadowClosed_refl _ _
  · exact mem_shadowClosed.mpr (Or.inr ⟨S, hS, hy, hx⟩)

omit [Fintype V] in
theorem shadowClosed_card (B : Finset (Finset V))
    (hB : ∀ S ∈ B, S.card = 5) (x : V) :
    (shadowClosed B x).card ≤ 1 + 5 * blockLoad B x := by
  calc
    _ ≤ ((B.filter fun S => x ∈ S).biUnion id).card + 1 := card_insert_le _ _
    _ ≤ (B.filter fun S => x ∈ S).card * 5 + 1 :=
      Nat.add_le_add_right (card_biUnion_le_card_mul _ _ _
        (fun S hS => (hB S (mem_filter.mp hS).1).le)) _
    _ = 1 + 5 * blockLoad B x := by simp [blockLoad, Nat.mul_comm, Nat.add_comm]

theorem sum_blockLoad (B : Finset (Finset V))
    (hB : ∀ S ∈ B, S.card = 5) : ∑ v : V, blockLoad B v = 5 * B.card := by
  have hcount := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := B) (t := (univ : Finset V)) (fun S v => v ∈ S)
  have habove (S : Finset V) :
      (univ.bipartiteAbove (fun S v => v ∈ S) S : Finset V) = S := by
    ext v
    simp [bipartiteAbove]
  simpa [habove, bipartiteBelow, blockLoad, sum_congr rfl hB, Nat.mul_comm] using hcount.symm

def saturated (B : Finset (Finset V)) (d : ℕ) : Finset V :=
  univ.filter fun v => d ≤ blockLoad B v

theorem saturated_card_mul_le (B : Finset (Finset V)) (d : ℕ)
    (hB : ∀ S ∈ B, S.card = 5) : (saturated B d).card * d ≤ 5 * B.card := by
  calc
    _ = ∑ _v ∈ saturated B d, d := by simp
    _ ≤ ∑ v ∈ saturated B d, blockLoad B v :=
      sum_le_sum fun v hv => (mem_filter.mp hv).2
    _ ≤ ∑ v : V, blockLoad B v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = 5 * B.card := sum_blockLoad B hB

omit [Fintype V] in
theorem blockLoad_insert {B : Finset (Finset V)} {S : Finset V} (hS : S ∉ B)
    (v : V) : blockLoad (insert S B) v = blockLoad B v + if v ∈ S then 1 else 0 := by
  by_cases hv : v ∈ S <;> simp [blockLoad, filter_insert, hv, hS]

/-- A construction history: a new five-set has no shadow route of at most three
steps between any of its distinct vertices. -/
inductive SeparatedFamily : Finset (Finset V) → Prop
  | empty : SeparatedFamily ∅
  | insert {B S} : SeparatedFamily B → S.card = 5 → S ∉ B →
      (S : Set V).Pairwise (fun x y => y ∉ threeStep (shadowClosed B) x) →
      SeparatedFamily (insert S B)

omit [Fintype V] in
theorem SeparatedFamily.card_blocks {B : Finset (Finset V)} (h : SeparatedFamily B) :
    ∀ S ∈ B, S.card = 5 := by
  induction h with
  | empty => simp
  | @insert B S hB hS hnot hsep ih =>
      intro T hT
      rcases mem_insert.mp hT with rfl | hT
      · exact hS
      · exact ih T hT

omit [Fintype V] in
theorem separated_not_mem {B : Finset (Finset V)} {S : Finset V}
    (hcard : S.card = 5)
    (hsep : (S : Set V).Pairwise (fun x y => y ∉ threeStep (shadowClosed B) x)) : S ∉ B := by
  intro hSB
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < S.card by omega)
  obtain ⟨y, hy, hxy⟩ := exists_mem_ne (show 1 < S.card by omega) x
  have hyC : y ∈ shadowClosed B x :=
    mem_shadowClosed.mpr (Or.inr ⟨S, hSB, hx, hy⟩)
  exact hsep hx hy (Ne.symm hxy)
    (mem_threeStep.mpr ⟨x, shadowClosed_refl _ _, x, shadowClosed_refl _ _, hyC⟩)

/-- Explicit finite greedy carrier existence. The two slack inequalities pay
for saturated vertices and the five forbidden three-step neighborhoods. -/
theorem exists_separated_family (d M : ℕ) (_hd : 0 < d)
    (hsat : 10 * M < d * Fintype.card V)
    (hball : 10 * (1 + 5 * d) ^ 3 < Fintype.card V) :
    ∃ B : Finset (Finset V), B.card = M ∧ SeparatedFamily B ∧
      ∀ v, blockLoad B v ≤ d := by
  have aux : ∀ m ≤ M, ∃ B : Finset (Finset V), B.card = m ∧ SeparatedFamily B ∧
      ∀ v, blockLoad B v ≤ d := by
    intro m hm
    induction m with
    | zero => exact ⟨∅, by simp, .empty, by simp [blockLoad]⟩
    | succ m ih =>
      obtain ⟨B, hBcard, hB, hcap⟩ := ih (by omega)
      have hload := saturated_card_mul_le B d hB.card_blocks
      have hsmall : 2 * (saturated B d).card < Fintype.card V := by
        rw [hBcard] at hload
        nlinarith
      have hroom : (saturated B d).card + 5 * (1 + 5 * d) ^ 3 < Fintype.card V := by
        omega
      have hshadow (x : V) : (shadowClosed B x).card ≤ 1 + 5 * d := by
        exact (shadowClosed_card B hB.card_blocks x).trans
          (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hcap x)) _)
      obtain ⟨S, hScard, hSA, hsep⟩ := exists_five_separated
        (shadowClosed B) (saturated B d) (1 + 5 * d) hshadow
        (shadowClosed_refl B) (shadowClosed_symm B) hroom
      have hSnot := separated_not_mem hScard hsep
      refine ⟨insert S B, by simp [hSnot, hBcard], .insert hB hScard hSnot hsep, ?_⟩
      intro v
      rw [blockLoad_insert hSnot]
      by_cases hv : v ∈ S
      · have hnotsat : v ∉ saturated B d := fun hv' => disjoint_left.mp hSA hv hv'
        have hlt : blockLoad B v < d := by simpa [saturated] using hnotsat
        simp only [hv, ite_true]
        omega
      · simpa [hv] using hcap v
  exact aux M le_rfl

abbrev carrierN : ℕ := 2 ^ 96
abbrev carrierM : ℕ := 120 * 96 * carrierN
abbrev carrierD : ℕ := 2 ^ 20

/-- A concrete carrier sufficient for the five-cycle assignment count. Its
astronomical size is symbolic; no enumeration is performed. -/
theorem exists_large_separated_family :
    ∃ B : Finset (Finset (Fin carrierN)), B.card = carrierM ∧ SeparatedFamily B := by
  obtain ⟨B, hcard, hsep, _⟩ :=
    exists_separated_family (V := Fin carrierN) carrierD carrierM
      (by norm_num [carrierD])
      (by norm_num [carrierD, carrierM, carrierN])
      (by norm_num [carrierD, carrierN])
  exact ⟨B, hcard, hsep⟩

end JSP000838
