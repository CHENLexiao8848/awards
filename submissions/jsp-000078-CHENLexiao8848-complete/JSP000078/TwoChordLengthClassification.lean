import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic

/-!
# Classifying the four lengths from two endpoint chords

The noncrossing configuration always supplies at least three lengths. In
the crossing configuration, at most two of the four constructed lengths
forces one of the two exceptional sets in Gyárfás's Lemma 6. This is a
statement about these explicit lengths, not a classification assumed for
all paths in an ambient graph.
-/

namespace JSP000078

/-- Four route lengths obtained from crossing endpoint chords. -/
def crossingChordLengths (L i j : ℕ) : Finset ℕ :=
  {L, L - i + 1, j + 1, i - j + 2}

/-- Four route lengths obtained from noncrossing endpoint chords. -/
def noncrossingChordLengths (L i j : ℕ) : Finset ℕ :=
  {L, L - i + 1, j + 1, j - i + 2}

/-- In a two-element set containing distinct `a,b`, every element is one
of those two. -/
private theorem eq_or_eq_of_card_le_two {S : Finset ℕ} {a b x : ℕ}
    (hS : S.card ≤ 2) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ S) :
    x = a ∨ x = b := by
  by_contra h
  have hxa : x ≠ a := fun hxa ↦ h (Or.inl hxa)
  have hxb : x ≠ b := fun hxb ↦ h (Or.inr hxb)
  have hcard : 2 < S.card := Finset.two_lt_card_iff.mpr
    ⟨a, b, x, ha, hb, hx, hab, Ne.symm hxa, Ne.symm hxb⟩
  omega

/-- Abstract crossing-length calculation. The total is larger than each
shortcut, so at most two values forces the shortcuts to coincide and the
middle route to equal either the shortcut or the total. -/
theorem crossing_lengths_two_values {a b d : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hd : 1 ≤ d)
    (hcard : ({a + b + d - 2, a, b, d + 2} : Finset ℕ).card ≤ 2) :
    ({a + b + d - 2, a, b, d + 2} : Finset ℕ) = {d + 2, 3 * d + 2} ∨
      ({a + b + d - 2, a, b, d + 2} : Finset ℕ) = {2, d + 2} := by
  let L := a + b + d - 2
  let S : Finset ℕ := {L, a, b, d + 2}
  have hS : S.card ≤ 2 := hcard
  have hLa : L ≠ a := by dsimp [L]; omega
  have hLb : L ≠ b := by dsimp [L]; omega
  have hLmem : L ∈ S := by simp [S]
  have hamem : a ∈ S := by simp [S]
  have hbmem : b ∈ S := by simp [S]
  have hdmem : d + 2 ∈ S := by simp [S]
  have hab : a = b := by
    rcases eq_or_eq_of_card_le_two hS hLmem hamem hLa hbmem with h | h
    · exact (hLb h.symm).elim
    · exact h.symm
  rcases eq_or_eq_of_card_le_two hS hLmem hamem hLa hdmem with heq | heq
  · have ha2 : a = 2 := by dsimp [L] at heq; omega
    have hb2 : b = 2 := by omega
    right
    subst a
    subst b
    ext n
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have haD : a = d + 2 := heq.symm
    have hbD : b = d + 2 := by omega
    left
    subst a
    subst b
    ext n
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- The two-value crossing exceptions have the original middle interval
length `i-j` as their parameter. -/
theorem crossingChordLengths_eq_exception {L i j : ℕ}
    (hj : 1 ≤ j) (hji : j < i) (hi : i < L)
    (hcard : (crossingChordLengths L i j).card ≤ 2) :
    crossingChordLengths L i j = {i - j + 2, 3 * (i - j) + 2} ∨
      crossingChordLengths L i j = {2, i - j + 2} := by
  have htotal : (L - i + 1) + (j + 1) + (i - j) - 2 = L := by omega
  have h := crossing_lengths_two_values
    (show 2 ≤ L - i + 1 by omega) (show 2 ≤ j + 1 by omega)
    (show 1 ≤ i - j by omega) (by
      simpa only [htotal, crossingChordLengths] using hcard)
  simpa only [htotal, crossingChordLengths] using h

/-- Crossing chords either give three different route lengths or have
one of the two explicit exceptional length sets. -/
theorem crossingChordLengths_three_or_exception {L i j : ℕ}
    (hj : 1 ≤ j) (hji : j < i) (hi : i < L) :
    3 ≤ (crossingChordLengths L i j).card ∨
      crossingChordLengths L i j = {i - j + 2, 3 * (i - j) + 2} ∨
      crossingChordLengths L i j = {2, i - j + 2} := by
  by_cases h : 3 ≤ (crossingChordLengths L i j).card
  · exact Or.inl h
  · exact Or.inr (crossingChordLengths_eq_exception hj hji hi (by omega))

/-- For proper noncrossing chords, the combined route, the shortcut from
the initial endpoint, and the original path form a strict three-length chain. -/
theorem three_le_card_noncrossingChordLengths {L i j : ℕ}
    (hi : 2 ≤ i) (hij : i ≤ j) (hj : j + 2 ≤ L) :
    3 ≤ (noncrossingChordLengths L i j).card := by
  have hchain₁ : j - i + 2 < L - i + 1 := by omega
  have hchain₂ : L - i + 1 < L := by omega
  have hcard : 2 < (noncrossingChordLengths L i j).card := by
    apply Finset.two_lt_card_iff.mpr
    refine ⟨j - i + 2, L - i + 1, L, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [noncrossingChordLengths]
    · simp [noncrossingChordLengths]
    · simp [noncrossingChordLengths]
    · omega
    · omega
    · omega
  omega

end JSP000078
