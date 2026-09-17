import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Filling the normalized marked positions on an odd cycle

Starting with the marked odd position three, closure by two fills all later
odd positions. A saturated reflected image then fills all positive even
positions. With zero marked and one absent, these are exactly the positions
of the cycle other than one.
-/

namespace JSP000078

/-- Closure of marked odd positions by two fills the odd interval starting
at three. The alternative terminal value cannot occur before a specified
position strictly below the bound. -/
theorem odd_positions_mem_of_three_mem_of_add_two_closed
    (X : Finset ℕ) (N : ℕ) (hthree : 3 ∈ X)
    (hclosed : ∀ d ∈ X.filter Odd, d + 2 ∈ X.filter Odd ∨ d + 2 = N) :
    ∀ n : ℕ, 3 ≤ n → n < N → Odd n → n ∈ X := by
  have hstep : ∀ m : ℕ, 3 + 2 * m < N → 3 + 2 * m ∈ X := by
    intro m
    induction m with
    | zero => simpa using fun _ : 3 < N ↦ hthree
    | succ m ih =>
        intro hm
        have hprev : 3 + 2 * m ∈ X := ih (by omega)
        have hodd : Odd (3 + 2 * m) := by
          rw [Nat.odd_iff]
          omega
        rcases hclosed (3 + 2 * m) (Finset.mem_filter.mpr ⟨hprev, hodd⟩) with hnext | hterm
        · have hmem := (Finset.mem_filter.mp hnext).1
          convert hmem using 1
        · omega
  intro n hn hnN hnOdd
  obtain ⟨m, hm⟩ := hnOdd
  have hrep : n = 3 + 2 * (m - 1) := by omega
  rw [hrep]
  exact hstep (m - 1) (by omega)

/-- The normalized closure and reflected-image relations force every cycle
position except one to be marked. There is no cardinality conclusion among
the hypotheses. -/
theorem normalized_odd_gap_closure_eq_range_erase
    (X : Finset ℕ) (N : ℕ) (hNodd : Odd N) (hN : 5 ≤ N)
    (hbound : ∀ n ∈ X, n < N) (hzero : 0 ∈ X) (hone : 1 ∉ X) (hthree : 3 ∈ X)
    (hclosed : ∀ d ∈ X.filter Odd, d + 2 ∈ X.filter Odd ∨ d + 2 = N)
    (hreflect : (X.filter fun e ↦ 0 < e ∧ Even e).image (fun e ↦ N - e + 2) =
      insert N (X.filter Odd)) :
    X = (Finset.range N).erase 1 := by
  classical
  have hoddFill := odd_positions_mem_of_three_mem_of_add_two_closed X N hthree hclosed
  have hrecover : ∀ e : ℕ, 0 < e → e < N → Even e → e ∈ X := by
    intro e hepos heN heEven
    have hemod := Nat.even_iff.mp heEven
    have hNmod := Nat.odd_iff.mp hNodd
    have he2 : 2 ≤ e := by omega
    have ht : N - e + 2 ∈ insert N (X.filter Odd) := by
      by_cases heq : e = 2
      · apply Finset.mem_insert.mpr
        left
        omega
      · apply Finset.mem_insert.mpr
        right
        have hge : 3 ≤ N - e + 2 := by omega
        have hlt : N - e + 2 < N := by omega
        have hOdd : Odd (N - e + 2) := by
          rw [Nat.odd_iff]
          omega
        exact Finset.mem_filter.mpr ⟨hoddFill _ hge hlt hOdd, hOdd⟩
    rw [← hreflect] at ht
    obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp ht
    have hdX := (Finset.mem_filter.mp hd).1
    have hdN := hbound d hdX
    have deq : d = e := by omega
    exact deq ▸ hdX
  ext n
  simp only [Finset.mem_erase, Finset.mem_range]
  constructor
  · intro hn
    exact ⟨fun h ↦ hone (h ▸ hn), hbound n hn⟩
  · rintro ⟨hnOne, hnN⟩
    by_cases hnZero : n = 0
    · exact hnZero ▸ hzero
    rcases Nat.even_or_odd n with he | ho
    · exact hrecover n (by omega) hnN he
    · apply hoddFill n _ hnN ho
      have hnmod := Nat.odd_iff.mp ho
      omega

end JSP000078
