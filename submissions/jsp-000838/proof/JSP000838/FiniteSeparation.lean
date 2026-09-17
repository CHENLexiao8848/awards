import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Pairwise.Basic

namespace JSP000838

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Endpoints of three successive closed-neighborhood steps. -/
def threeStep (C : V → Finset V) (x : V) : Finset V :=
  (C x).biUnion fun y => (C y).biUnion C

omit [Fintype V] in
theorem mem_threeStep {C : V → Finset V} {x y : V} :
    y ∈ threeStep C x ↔ ∃ a ∈ C x, ∃ b ∈ C a, y ∈ C b := by
  simp [threeStep]

omit [Fintype V] in
theorem threeStep_card_le {C : V → Finset V} {D : ℕ}
    (hC : ∀ x, (C x).card ≤ D) (x : V) : (threeStep C x).card ≤ D ^ 3 := by
  have htwo (y : V) : ((C y).biUnion C).card ≤ D * D := by
    calc
      _ ≤ (C y).card * D := card_biUnion_le_card_mul _ _ _ (fun z _ => hC z)
      _ ≤ D * D := Nat.mul_le_mul_right _ (hC y)
  calc
    _ ≤ (C x).card * (D * D) := card_biUnion_le_card_mul _ _ _ (fun y _ => htwo y)
    _ ≤ D * (D * D) := Nat.mul_le_mul_right _ (hC x)
    _ = D ^ 3 := by ring

omit [Fintype V] in
theorem threeStep_refl {C : V → Finset V} (hrefl : ∀ x, x ∈ C x) (x : V) :
    x ∈ threeStep C x :=
  mem_threeStep.mpr ⟨x, hrefl x, x, hrefl x, hrefl x⟩

omit [Fintype V] in
theorem threeStep_symm {C : V → Finset V}
    (hsymm : ∀ x y, y ∈ C x → x ∈ C y) {x y : V}
    (h : y ∈ threeStep C x) : x ∈ threeStep C y := by
  obtain ⟨a, hxa, b, hab, hby⟩ := mem_threeStep.mp h
  exact mem_threeStep.mpr ⟨b, hsymm _ _ hby, a, hsymm _ _ hab, hsymm _ _ hxa⟩

/-- A finite greedy packing lemma, with explicit room for the exceptional set
and all forbidden neighborhoods. -/
theorem exists_separated_finset (F : V → Finset V) (A : Finset V)
    (B p : ℕ) (hcard : ∀ x, (F x).card ≤ B)
    (hrefl : ∀ x, x ∈ F x) (hsymm : ∀ x y, y ∈ F x → x ∈ F y)
    (hroom : A.card + p * B < Fintype.card V) :
    ∃ S : Finset V, S.card = p ∧ Disjoint S A ∧
      (S : Set V).Pairwise (fun x y => y ∉ F x) := by
  have aux : ∀ k ≤ p, ∃ S : Finset V, S.card = k ∧ Disjoint S A ∧
      (S : Set V).Pairwise (fun x y => y ∉ F x) := by
    intro k hk
    induction k with
    | zero => exact ⟨∅, by simp, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨S, hS, hSA, hsep⟩ := ih (by omega)
      let banned := A ∪ S.biUnion F
      have hbanned : banned.card < Fintype.card V := by
        calc
          banned.card ≤ A.card + (S.biUnion F).card := card_union_le _ _
          _ ≤ A.card + S.card * B :=
            Nat.add_le_add_left (card_biUnion_le_card_mul _ _ _ (fun x _ => hcard x)) _
          _ = A.card + k * B := by rw [hS]
          _ ≤ A.card + p * B := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
          _ < Fintype.card V := hroom
      obtain ⟨x, _, hx⟩ := exists_mem_notMem_of_card_lt_card
        (show banned.card < (univ : Finset V).card by simpa using hbanned)
      have hxA : x ∉ A := fun h => hx (mem_union_left _ h)
      have hxF : ∀ y ∈ S, x ∉ F y := fun y hy hxy =>
        hx (mem_union_right _ (mem_biUnion.mpr ⟨y, hy, hxy⟩))
      have hxS : x ∉ S := fun h => hxF x h (hrefl x)
      refine ⟨insert x S, by simp [hxS, hS], ?_, ?_⟩
      · exact disjoint_insert_left.mpr ⟨hxA, hSA⟩
      · intro a ha b hb hab
        rcases mem_insert.mp ha with rfl | haOld
        · rcases mem_insert.mp hb with rfl | hbOld
          · exact (hab rfl).elim
          · exact fun h => hxF b hbOld (hsymm _ _ h)
        · rcases mem_insert.mp hb with rfl | hbOld
          · exact hxF a haOld
          · exact hsep haOld hbOld hab
  exact aux p le_rfl

/-- Closed neighborhoods of bounded cardinal have a separated five-set. -/
theorem exists_five_separated (C : V → Finset V) (A : Finset V) (D : ℕ)
    (hcard : ∀ x, (C x).card ≤ D) (hrefl : ∀ x, x ∈ C x)
    (hsymm : ∀ x y, y ∈ C x → x ∈ C y)
    (hroom : A.card + 5 * D ^ 3 < Fintype.card V) :
    ∃ S : Finset V, S.card = 5 ∧ Disjoint S A ∧
      (S : Set V).Pairwise (fun x y => y ∉ threeStep C x) :=
  exists_separated_finset (threeStep C) A (D ^ 3) 5
    (threeStep_card_le hcard) (threeStep_refl hrefl)
    (fun _ _ => threeStep_symm hsymm) hroom

end JSP000838
