import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Problems.JSP000633Counting
import Problems.JSP000633Algebra
import Problems.JSP000633Asymptotic

/-!
# JSP-000633 / Erdős problem 772

Ordered pair representation counts include diagonal pairs. Sidon means that
all equal two-term sums have the same unordered pair, including repeated terms.
-/
namespace JSP000633
open Finset
open scoped BigOperators

/-- The number of ordered representations of `s` as a sum from `A`. -/
def representations (A : Finset ℕ) (s : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun ab => ab.1 + ab.2 = s).card

/-- Uniform bound on the ordered convolution `1_A * 1_A`. -/
def BoundedRepresentations (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ s, representations A s ≤ k

/-- A Sidon set, with repeated summands included. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Delete at most one vertex per nonempty forbidden set. -/
theorem delete_forbidden {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Finset (Finset α))
    (hF : ∀ e ∈ F, e.Nonempty) :
    ∃ B ⊆ A, (∀ e ∈ F, ¬e ⊆ B) ∧ A.card ≤ B.card + F.card := by
  induction F using Finset.induction_on with
  | empty => exact ⟨A, Subset.rfl, by simp⟩
  | @insert e F he ih =>
    obtain ⟨B, hBA, hBF, hcard⟩ := ih (by intro e he; exact hF e (mem_insert_of_mem he))
    by_cases heB : e ⊆ B
    · obtain ⟨x, hx⟩ := hF e (mem_insert_self _ _)
      refine ⟨B.erase x, (erase_subset _ _).trans hBA, ?_, ?_⟩
      · intro f hf
        rcases mem_insert.mp hf with rfl | hf
        · intro h; exact (mem_erase.mp (h hx)).1 rfl
        · exact fun h => hBF f hf (h.trans (erase_subset _ _))
      · have hxB := heB hx
        rw [card_insert_of_notMem he, card_erase_of_mem hxB]
        have := card_pos.mpr ⟨x, hxB⟩
        omega
    · refine ⟨B, hBA, ?_, ?_⟩
      · simpa only [mem_insert, forall_eq_or_imp] using And.intro heB hBF
      · rw [card_insert_of_notMem he]; omega

/-- The Bernoulli weight of a subset, expressed as a finite product. -/
noncomputable def sampleWeight {α : Type*} [DecidableEq α]
    (p : ℝ) (A S : Finset α) : ℝ :=
  ∏ a ∈ A, if a ∈ S then p else 1 - p

lemma sampleWeight_nonneg {α : Type*} [DecidableEq α]
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (A S : Finset α) :
    0 ≤ sampleWeight p A S := by
  unfold sampleWeight
  apply Finset.prod_nonneg
  intro a ha
  split_ifs <;> linarith

lemma sampleWeight_insert_absent {α : Type*} [DecidableEq α]
    (p : ℝ) (A S : Finset α) (a : α) (ha : a ∉ A) (hS : S ⊆ A) :
    sampleWeight p (insert a A) S = (1-p) * sampleWeight p A S := by
  have haS : a ∉ S := fun h => ha (hS h)
  simp [sampleWeight, ha, haS]

lemma sampleWeight_insert_present {α : Type*} [DecidableEq α]
    (p : ℝ) (A S : Finset α) (a : α) (ha : a ∉ A) :
    sampleWeight p (insert a A) (insert a S) = p * sampleWeight p A S := by
  rw [sampleWeight, prod_insert ha]
  simp only [mem_insert_self, ↓reduceIte]
  congr 1
  apply prod_congr rfl
  intro b hb
  have hba : b ≠ a := by rintro rfl; exact ha hb
  simp [hba]

lemma sampleWeight_sum {α : Type*} [DecidableEq α] (p : ℝ) (A : Finset α) :
    ∑ S ∈ A.powerset, sampleWeight p A S = 1 := by
  induction A using Finset.induction_on with
  | empty => simp [sampleWeight]
  | @insert a A ha ih =>
    rw [sum_powerset_insert ha]
    have h₁ : (∑ S ∈ A.powerset, sampleWeight p (insert a A) S) =
        (1-p) * ∑ S ∈ A.powerset, sampleWeight p A S := by
      rw [mul_sum]
      exact sum_congr rfl (fun S hS => sampleWeight_insert_absent p A S a ha (mem_powerset.mp hS))
    have h₂ : (∑ S ∈ A.powerset, sampleWeight p (insert a A) (insert a S)) =
        p * ∑ S ∈ A.powerset, sampleWeight p A S := by
      rw [mul_sum]
      exact sum_congr rfl (fun S _ => sampleWeight_insert_present p A S a ha)
    rw [h₁, h₂, ih]
    ring

/-- The probability that every vertex of a specified set is selected. -/
lemma sampleWeight_containing {α : Type*} [DecidableEq α]
    (p : ℝ) (A e : Finset α) (he : e ⊆ A) :
    (∑ S ∈ A.powerset, if e ⊆ S then sampleWeight p A S else 0) = p ^ e.card := by
  induction A using Finset.induction_on generalizing e with
  | empty =>
    have : e = ∅ := subset_empty.mp he
    subst e
    simp [sampleWeight]
  | @insert a A ha ih =>
    rw [sum_powerset_insert ha]
    by_cases hae : a ∈ e
    · have heA : e.erase a ⊆ A := subset_insert_iff.mp he
      have h₁ : (∑ S ∈ A.powerset, if e ⊆ S then sampleWeight p (insert a A) S else 0) = 0 := by
        apply sum_eq_zero
        intro S hS
        have hnot : ¬e ⊆ S := fun h => ha ((mem_powerset.mp hS) (h hae))
        simp [hnot]
      have h₂ : (∑ S ∈ A.powerset,
          if e ⊆ insert a S then sampleWeight p (insert a A) (insert a S) else 0) =
          p * ∑ S ∈ A.powerset, if e.erase a ⊆ S then sampleWeight p A S else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S hS
        simp only [subset_insert_iff, sampleWeight_insert_present p A S a ha]
        split_ifs <;> ring
      rw [h₁, h₂, ih _ heA, zero_add]
      have hc : e.card = (e.erase a).card + 1 := by
        rw [card_erase_of_mem hae]
        exact (Nat.sub_add_cancel (card_pos.mpr ⟨a, hae⟩)).symm
      rw [hc, pow_succ]
      ring
    · have heA : e ⊆ A := (subset_insert_iff_of_notMem hae).mp he
      have h₁ : (∑ S ∈ A.powerset, if e ⊆ S then sampleWeight p (insert a A) S else 0) =
          (1-p) * ∑ S ∈ A.powerset, if e ⊆ S then sampleWeight p A S else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S hS
        rw [sampleWeight_insert_absent p A S a ha (mem_powerset.mp hS)]
        split_ifs <;> ring
      have h₂ : (∑ S ∈ A.powerset,
          if e ⊆ insert a S then sampleWeight p (insert a A) (insert a S) else 0) =
          p * ∑ S ∈ A.powerset, if e ⊆ S then sampleWeight p A S else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S hS
        simp only [subset_insert_iff_of_notMem hae, sampleWeight_insert_present p A S a ha]
        split_ifs <;> ring
      rw [h₁, h₂, ih _ heA]
      ring

/-- Expected size of a Bernoulli sample. -/
lemma sampleWeight_card {α : Type*} [DecidableEq α] (p : ℝ) (A : Finset α) :
    (∑ S ∈ A.powerset, sampleWeight p A S * (S.card : ℝ)) = p * A.card := by
  have hcard (S : Finset α) (hS : S ∈ A.powerset) :
      (S.card : ℝ) = ∑ a ∈ A, if a ∈ S then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    have : A.filter (fun a => a ∈ S) = S := by
      ext a
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun ha => (mem_powerset.mp hS) ha)
    simp [this]
  calc
    (∑ S ∈ A.powerset, sampleWeight p A S * (S.card : ℝ)) =
        ∑ S ∈ A.powerset, ∑ a ∈ A, if a ∈ S then sampleWeight p A S else 0 := by
      apply sum_congr rfl
      intro S hS
      rw [hcard S hS, mul_sum]
      apply sum_congr rfl
      intro a ha
      split_ifs <;> simp_all
    _ = ∑ a ∈ A, ∑ S ∈ A.powerset, if a ∈ S then sampleWeight p A S else 0 := sum_comm
    _ = ∑ a ∈ A, p := by
      apply sum_congr rfl
      intro a ha
      simpa using sampleWeight_containing p A {a} (singleton_subset_iff.mpr ha)
    _ = p * A.card := by simp [mul_comm]

/-- Weighted expected number of forbidden sets that survive sampling. -/
lemma sampleWeight_forbidden {α : Type*} [DecidableEq α]
    (p : ℝ) (A : Finset α) (F : Finset (Finset α))
    (hFA : ∀ e ∈ F, e ⊆ A) :
    (∑ S ∈ A.powerset, sampleWeight p A S * ((F.filter (fun e => e ⊆ S)).card : ℝ)) =
    ∑ e ∈ F, p ^ e.card := by
  calc
    (∑ S ∈ A.powerset, sampleWeight p A S * ((F.filter (fun e => e ⊆ S)).card : ℝ)) =
        ∑ S ∈ A.powerset, ∑ e ∈ F, if e ⊆ S then sampleWeight p A S else 0 := by
      apply sum_congr rfl
      intro S hS
      rw [← sum_boole, mul_sum]
      apply sum_congr rfl
      intro e he
      split_ifs <;> simp_all
    _ = ∑ e ∈ F, ∑ S ∈ A.powerset, if e ⊆ S then sampleWeight p A S else 0 := sum_comm
    _ = ∑ e ∈ F, p ^ e.card := sum_congr rfl (fun e he => sampleWeight_containing p A e (hFA e he))

/-- A finite form of the alteration method, valid for arbitrary forbidden finite sets. -/
theorem alteration {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Finset (Finset α)) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hFA : ∀ e ∈ F, e ⊆ A) (hF : ∀ e ∈ F, e.Nonempty) :
    ∃ B ⊆ A, (∀ e ∈ F, ¬e ⊆ B) ∧
      p * A.card - (∑ e ∈ F, p ^ e.card) ≤ (B.card : ℝ) := by
  let score (S : Finset α) : ℝ := S.card - (F.filter (fun e => e ⊆ S)).card
  obtain ⟨S, hSA, hmax⟩ := exists_max_image A.powerset score ⟨∅, by simp⟩
  have hscore : p * A.card - (∑ e ∈ F, p ^ e.card) ≤ score S := by
    calc
      p * A.card - (∑ e ∈ F, p ^ e.card) =
          ∑ T ∈ A.powerset, sampleWeight p A T * score T := by
        simp only [score, mul_sub, sum_sub_distrib]
        rw [sampleWeight_card, sampleWeight_forbidden p A F hFA]
      _ ≤ ∑ T ∈ A.powerset, sampleWeight p A T * score S :=
        sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left (hmax T hT) (sampleWeight_nonneg hp hp1 A T))
      _ = score S := by rw [← sum_mul, sampleWeight_sum, one_mul]
  obtain ⟨B, hBS, hBF, hcard⟩ := delete_forbidden S (F.filter (fun e => e ⊆ S))
    (by intro e he; exact hF e (mem_filter.mp he).1)
  refine ⟨B, hBS.trans (mem_powerset.mp hSA), ?_, ?_⟩
  · intro e he heB
    exact hBF e (mem_filter.mpr ⟨he, heB.trans hBS⟩) heB
  · have hc : (S.card : ℝ) ≤ B.card + (F.filter (fun e => e ⊆ S)).card := by exact_mod_cast hcard
    dsimp [score] at hscore
    linarith

/-- Alteration with separate three-vertex and four-vertex forbidden configurations. -/
theorem alteration_three_four {α : Type*} [DecidableEq α]
    (A : Finset α) (F₃ F₄ : Finset (Finset α)) (k p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (h₃A : ∀ e ∈ F₃, e ⊆ A) (h₄A : ∀ e ∈ F₄, e ⊆ A)
    (h₃ : ∀ e ∈ F₃, e.card = 3) (h₄ : ∀ e ∈ F₄, e.card = 4)
    (hc₃ : (F₃.card : ℝ) ≤ k * A.card)
    (hc₄ : (F₄.card : ℝ) ≤ k * (A.card : ℝ)^2) :
    ∃ B ⊆ A, (∀ e ∈ F₃, ¬e ⊆ B) ∧ (∀ e ∈ F₄, ¬e ⊆ B) ∧
      p * A.card - k * A.card * p^3 - k * (A.card : ℝ)^2 * p^4 ≤ (B.card : ℝ) := by
  have hdisj : Disjoint F₃ F₄ := by
    apply disjoint_left.mpr
    intro e he₃ he₄
    have := h₃ e he₃
    have := h₄ e he₄
    omega
  have hF : ∀ e ∈ F₃ ∪ F₄, e.Nonempty := by
    intro e he
    apply card_pos.mp
    rcases mem_union.mp he with he | he
    · rw [h₃ e he]; decide
    · rw [h₄ e he]; decide
  have hFA : ∀ e ∈ F₃ ∪ F₄, e ⊆ A := by
    intro e he
    exact (mem_union.mp he).elim (h₃A e) (h₄A e)
  obtain ⟨B, hBA, hBF, hsize⟩ := alteration A (F₃ ∪ F₄) p hp hp1 hFA hF
  refine ⟨B, hBA, (fun e he => hBF e (mem_union_left F₄ he)),
    (fun e he => hBF e (mem_union_right F₃ he)), ?_⟩
  have hsum₃ : (∑ e ∈ F₃, p ^ e.card) = F₃.card * p^3 := by
    rw [sum_congr rfl (fun e he => congrArg (p ^ ·) (h₃ e he))]
    simp
  have hsum₄ : (∑ e ∈ F₄, p ^ e.card) = F₄.card * p^4 := by
    rw [sum_congr rfl (fun e he => congrArg (p ^ ·) (h₄ e he))]
    simp
  rw [sum_union hdisj, hsum₃, hsum₄] at hsize
  have he₃ := mul_le_mul_of_nonneg_right hc₃ (pow_nonneg hp 3)
  have he₄ := mul_le_mul_of_nonneg_right hc₄ (pow_nonneg hp 4)
  linarith

lemma isSidon_empty : IsSidon ∅ := by simp [IsSidon]

lemma isSidon_singleton (a : ℕ) : IsSidon {a} := by
  intro b hb c hc d hd e he hsum
  simp only [mem_singleton] at hb hc hd he
  exact Or.inl ⟨hb.trans hd.symm, hc.trans he.symm⟩

/-- The largest Sidon subset exists in the finite powerset. -/
theorem exists_largest_sidon (A : Finset ℕ) :
    ∃ B ⊆ A, IsSidon B ∧ ∀ S ⊆ A, IsSidon S → S.card ≤ B.card := by
  classical
  let T := A.powerset.filter IsSidon
  have hT : T.Nonempty := ⟨∅, by simp [T, isSidon_empty]⟩
  obtain ⟨B, hB, hmax⟩ := exists_max_image T card hT
  obtain ⟨hBA, hSidon⟩ := mem_filter.mp hB
  exact ⟨B, mem_powerset.mp hBA, hSidon,
    fun S hSA hS => hmax S (mem_filter.mpr ⟨mem_powerset.mpr hSA, hS⟩)⟩

/-- The explicit finite lower bound behind the answer to Erdős problem 772. -/
theorem finite_bound (A : Finset ℕ) (k : ℕ) (hk : BoundedRepresentations A k) :
    ∃ B ⊆ A, IsSidon B ∧
      (A.card : ℝ)^2 ≤ (4 + 24 * (k : ℝ)) * (B.card : ℝ)^3 := by
  obtain ⟨B, hBA, hSidon, hmax⟩ := exists_largest_sidon A
  refine ⟨B, hBA, hSidon, ?_⟩
  by_cases hA : A = ∅
  · subst A
    have : B = ∅ := subset_empty.mp hBA
    simp [this]
  have hn : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hA)
  have hm : (1 : ℝ) ≤ B.card := by
    obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr hA
    have h := hmax {a} (singleton_subset_iff.mpr ha) (isSidon_singleton a)
    simpa using (Nat.cast_le (α := ℝ)).mpr h
  apply polynomial_of_alteration (A.card : ℝ) (B.card : ℝ) (k : ℝ) hn hm (Nat.cast_nonneg k)
  intro p hp hp1
  have hkcount : ∀ s, (Counting.pairs A s).card ≤ k := hk
  have hc₃ : ((Counting.F3 A).card : ℝ) ≤ k * A.card := by
    exact_mod_cast (Counting.card_F3_le A k hkcount).trans_eq (Nat.mul_comm _ _)
  have hc₄ : ((Counting.F4 A).card : ℝ) ≤ k * (A.card : ℝ)^2 := by
    exact_mod_cast (Counting.card_F4_le A k hkcount).trans_eq (Nat.mul_comm _ _)
  obtain ⟨S, hSA, hS₃, hS₄, hsize⟩ := alteration_three_four A (Counting.F3 A) (Counting.F4 A) k p hp hp1
    (fun _ he => (Counting.F3_spec he).1) (fun _ he => (Counting.F4_spec he).1)
    (fun _ he => (Counting.F3_spec he).2) (fun _ he => (Counting.F4_spec he).2) hc₃ hc₄
  have hSSidon : IsSidon S := Counting.avoids_imp_sidon hSA hS₃ hS₄
  exact hsize.trans (by exact_mod_cast hmax S hSA hSSidon)

/-- A uniform positive constant times the two-thirds power of the size. -/
theorem sidon_subset_two_thirds (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℕ, BoundedRepresentations A k →
      ∃ B ⊆ A, IsSidon B ∧ c * (A.card : ℝ) ^ (2/3 : ℝ) ≤ B.card := by
  let C : ℝ := 4 + 24 * (k : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1 / C ^ (1/3 : ℝ), div_pos zero_lt_one (Real.rpow_pos_of_pos hC _), ?_⟩
  intro A hk
  obtain ⟨B, hBA, hB, hsize⟩ := finite_bound A k hk
  exact ⟨B, hBA, hB, cubic_bound_implies_rpow_bound
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC hsize⟩

/-- Every fixed multiple of square root is eventually exceeded, uniformly over all admissible sets. -/
theorem exceeds_every_sqrt_multiple (k : ℕ) (M : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ, A.card = n → BoundedRepresentations A k →
      ∃ B ⊆ A, IsSidon B ∧ M * Real.sqrt n < (B.card : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := sidon_subset_two_thirds k
  filter_upwards [eventually_sqrt_multiple (M := M) hc] with n hn
  intro A hAn hk
  obtain ⟨B, hBA, hB, hsize⟩ := hbound A hk
  rw [hAn] at hsize
  exact ⟨B, hBA, hB, hn.trans_le hsize⟩

/-- The requested positive exponent improvement, with exponent one-half plus one-twelfth. -/
theorem positive_power_improvement (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ, A.card = n → BoundedRepresentations A k →
      ∃ B ⊆ A, IsSidon B ∧ (n : ℝ) ^ (1/2 + 1/12 : ℝ) < (B.card : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := sidon_subset_two_thirds k
  filter_upwards [eventually_positive_power_improvement hc] with n hn
  intro A hAn hk
  obtain ⟨B, hBA, hB, hsize⟩ := hbound A hk
  rw [hAn] at hsize
  exact ⟨B, hBA, hB, hn.trans_le hsize⟩

/-- The first question in threshold form. -/
theorem answer_sqrt (k : ℕ) (M : ℝ) :
    ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card → BoundedRepresentations A k →
      ∃ B ⊆ A, IsSidon B ∧ M * Real.sqrt A.card < (B.card : ℝ) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (exceeds_every_sqrt_multiple k M)
  exact ⟨N, fun A hA hk => hN A.card hA A rfl hk⟩

/-- The second question in threshold form, with the fixed positive improvement `1/12`. -/
theorem answer_positive_power (k : ℕ) :
    ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card → BoundedRepresentations A k →
      ∃ B ⊆ A, IsSidon B ∧ (A.card : ℝ) ^ (1/2 + 1/12 : ℝ) < (B.card : ℝ) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (positive_power_improvement k)
  exact ⟨N, fun A hA hk => hN A.card hA A rfl hk⟩

end JSP000633
