import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

namespace JSP000633.Counting
open Finset
open scoped BigOperators

def pairs (A : Finset ℕ) (s : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun ab => ab.1 + ab.2 = s)

def triplesAt (A : Finset ℕ) (a : ℕ) : Finset (Finset ℕ) :=
  ((pairs A (2*a)).filter (fun bc => bc.1 ≠ bc.2)).image
    (fun bc => {a, bc.1, bc.2})

def F3 (A : Finset ℕ) : Finset (Finset ℕ) := A.biUnion (triplesAt A)

def Distinct4 (a b c d : ℕ) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

instance (a b c d : ℕ) : Decidable (Distinct4 a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def quadsAt (A : Finset ℕ) (ab : ℕ × ℕ) : Finset (Finset ℕ) :=
  ((pairs A (ab.1+ab.2)).filter (fun cd => Distinct4 ab.1 ab.2 cd.1 cd.2)).image
    (fun cd => {ab.1, ab.2, cd.1, cd.2})

def F4 (A : Finset ℕ) : Finset (Finset ℕ) := (A ×ˢ A).biUnion (quadsAt A)

theorem card_F3_le (A : Finset ℕ) (k : ℕ) (hk : ∀ s, (pairs A s).card ≤ k) :
    (F3 A).card ≤ A.card * k := by
  apply card_biUnion_le_card_mul
  intro a ha
  exact card_image_le.trans ((card_filter_le _ _).trans (hk (2*a)))

theorem card_F4_le (A : Finset ℕ) (k : ℕ) (hk : ∀ s, (pairs A s).card ≤ k) :
    (F4 A).card ≤ A.card ^ 2 * k := by
  have h : (F4 A).card ≤ (A ×ˢ A).card * k := by
    apply card_biUnion_le_card_mul
    intro ab hab
    exact card_image_le.trans ((card_filter_le _ _).trans (hk (ab.1+ab.2)))
  simpa [card_product, pow_two] using h

theorem mem_F3_iff (A e : Finset ℕ) :
    e ∈ F3 A ↔ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      b + c = 2*a ∧ b ≠ c ∧ e = {a,b,c} := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := mem_biUnion.mp h
    obtain ⟨bc, hbc, heq⟩ := mem_image.mp he
    obtain ⟨hp, hne⟩ := mem_filter.mp hbc
    obtain ⟨hab, hs⟩ := mem_filter.mp hp
    obtain ⟨hb, hc⟩ := mem_product.mp hab
    exact ⟨a, ha, bc.1, hb, bc.2, hc, hs, hne, heq.symm⟩
  · rintro ⟨a, ha, b, hb, c, hc, hs, hne, rfl⟩
    apply mem_biUnion.mpr
    refine ⟨a, ha, mem_image.mpr ⟨(b,c), ?_, rfl⟩⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hb,hc⟩, hs⟩, hne⟩

theorem mem_F4_iff (A e : Finset ℕ) :
    e ∈ F4 A ↔ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
      c+d = a+b ∧ Distinct4 a b c d ∧ e = {a,b,c,d} := by
  constructor
  · intro h
    obtain ⟨ab, hab, he⟩ := mem_biUnion.mp h
    obtain ⟨cd, hcd, heq⟩ := mem_image.mp he
    obtain ⟨hp, hdist⟩ := mem_filter.mp hcd
    obtain ⟨hcd, hs⟩ := mem_filter.mp hp
    exact ⟨ab.1, (mem_product.mp hab).1, ab.2, (mem_product.mp hab).2,
      cd.1, (mem_product.mp hcd).1, cd.2, (mem_product.mp hcd).2, hs, hdist, heq.symm⟩
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, hs, hdist, rfl⟩
    apply mem_biUnion.mpr
    refine ⟨(a,b), mem_product.mpr ⟨ha,hb⟩, mem_image.mpr ⟨(c,d), ?_, rfl⟩⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hc,hd⟩, hs⟩, hdist⟩

theorem F3_spec {A e : Finset ℕ} (he : e ∈ F3 A) : e ⊆ A ∧ e.card = 3 := by
  obtain ⟨a, ha, b, hb, c, hc, hs, hne, rfl⟩ := (mem_F3_iff A e).mp he
  have hab : a ≠ b := by omega
  have hac : a ≠ c := by omega
  constructor
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simp [hab,hac,hne]

theorem F4_spec {A e : Finset ℕ} (he : e ∈ F4 A) : e ⊆ A ∧ e.card = 4 := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hs, hdist, rfl⟩ := (mem_F4_iff A e).mp he
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := hdist
  constructor
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · simp [hab,hac,had,hbc,hbd,hcd]

theorem avoids_imp_sidon {A B : Finset ℕ} (hBA : B ⊆ A)
    (h3 : ∀ e ∈ F3 A, ¬ e ⊆ B) (h4 : ∀ e ∈ F4 A, ¬ e ⊆ B) :
    ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
      a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  intro a ha b hb c hc d hd hs
  by_cases hac : a=c
  · exact Or.inl ⟨hac, by omega⟩
  by_cases had : a=d
  · exact Or.inr ⟨had, by omega⟩
  have hbc : b≠c := by omega
  have hbd : b≠d := by omega
  by_cases hab : a=b
  · exfalso
    have hcd : c≠d := by omega
    apply h3 {a,c,d} ((mem_F3_iff _ _).mpr
      ⟨a,hBA ha,c,hBA hc,d,hBA hd,by omega,hcd,rfl⟩)
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  by_cases hcd : c=d
  · exfalso
    apply h3 {c,a,b} ((mem_F3_iff _ _).mpr
      ⟨c,hBA hc,a,hBA ha,b,hBA hb,by omega,hab,rfl⟩)
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · exfalso
    apply h4 {a,b,c,d} ((mem_F4_iff _ _).mpr
      ⟨a,hBA ha,b,hBA hb,c,hBA hc,d,hBA hd,hs.symm,⟨hab,hac,had,hbc,hbd,hcd⟩,rfl⟩)
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

end JSP000633.Counting
