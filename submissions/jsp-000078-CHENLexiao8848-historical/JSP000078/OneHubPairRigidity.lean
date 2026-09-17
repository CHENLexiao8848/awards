import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Rigidity with one odd length and two hub attachments

When the only odd cycle length is `N`, two ordered attachment positions
and their mixed outside-path cycles force the positions to be `1` and
`N - 1`. The outside path then has positive even length `N - 3`.
-/

namespace JSP000078

/-- The arithmetic boundary configuration for two distinct attachment
positions when the available odd-length set has cardinality one. -/
theorem one_hub_pair_rigidity
    (K : Finset ℕ) (N L a b : ℕ) (hN : Odd N) (hL : 1 ≤ L)
    (ha : 1 ≤ a) (hab : a < b) (hb : b < N)
    (hK : K.card = 1) (hNmem : N ∈ K)
    (hA : Odd (L + a + 2) → L + a + 2 ∈ K)
    (hAcomp : Odd (L + (N - a) + 2) → L + (N - a) + 2 ∈ K)
    (hB : Odd (L + b + 2) → L + b + 2 ∈ K)
    (hBcomp : Odd (L + (N - b) + 2) → L + (N - b) + 2 ∈ K)
    (hSpoke : Odd (b - a + 2) → b - a + 2 ∈ K) :
    a = 1 ∧ b = N - 1 ∧ Even L ∧ L + 3 = N ∧ 5 ≤ N := by
  have heq : ∀ n ∈ K, n = N := by
    obtain ⟨m, hKm⟩ := Finset.card_eq_one.mp hK
    have hNm : N = m := by simpa only [hKm, Finset.mem_singleton] using hNmem
    intro n hn
    have hnm : n = m := by simpa only [hKm, Finset.mem_singleton] using hn
    exact hnm.trans hNm.symm
  have hNmod := Nat.odd_iff.mp hN
  have hAeq : (L + a + 2) % 2 = 1 → L + a + 2 = N :=
    fun h ↦ heq _ (hA (Nat.odd_iff.mpr h))
  have hAcompeq : (L + (N - a) + 2) % 2 = 1 → L + (N - a) + 2 = N :=
    fun h ↦ heq _ (hAcomp (Nat.odd_iff.mpr h))
  have hBeq : (L + b + 2) % 2 = 1 → L + b + 2 = N :=
    fun h ↦ heq _ (hB (Nat.odd_iff.mpr h))
  have hBcompeq : (L + (N - b) + 2) % 2 = 1 → L + (N - b) + 2 = N :=
    fun h ↦ heq _ (hBcomp (Nat.odd_iff.mpr h))
  have hSpokeeq : (b - a + 2) % 2 = 1 → b - a + 2 = N :=
    fun h ↦ heq _ (hSpoke (Nat.odd_iff.mpr h))
  have habpar : a % 2 ≠ b % 2 := by omega
  have hSpokeN : b - a + 2 = N := hSpokeeq (by omega)
  have haone : a = 1 := by omega
  have hblast : b = N - 1 := by omega
  have hLeven : Even L := Nat.even_iff.mpr (by omega)
  have hLmod := Nat.even_iff.mp hLeven
  exact ⟨haone, hblast, hLeven, by omega, by omega⟩

end JSP000078
