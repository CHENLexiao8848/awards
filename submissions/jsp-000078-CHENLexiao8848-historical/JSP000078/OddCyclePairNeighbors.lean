import JSP000078.CyclePositions

/-!
# A cycle vertex is determined by its two rim neighbors

On a simple cycle of length at least five, two different vertices cannot
have the same unordered pair of predecessor and successor vertices. This
rules out the duplicated-neighbor boundary configuration in the one-odd-
length case; only actual rim neighbors, not arbitrary ambient edges, are
used.
-/

namespace JSP000078

/-- Previous canonical index on a cycle. -/
def rimPrevIndex (N i : ℕ) : ℕ := (i + N - 1) % N

/-- Next canonical index on a cycle. -/
def rimNextIndex (N i : ℕ) : ℕ := (i + 1) % N

theorem rimPrevIndex_eq {N i : ℕ} (hN : 1 ≤ N) (hi : i < N) :
    rimPrevIndex N i = if i = 0 then N - 1 else i - 1 := by
  unfold rimPrevIndex
  split_ifs with hizero
  · subst i
    simp only [Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
  · have heq : i + N - 1 = (i - 1) + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem rimNextIndex_eq {N i : ℕ} (hi : i < N) :
    rimNextIndex N i = if i + 1 = N then 0 else i + 1 := by
  unfold rimNextIndex
  split_ifs with hilast
  · rw [hilast, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- An unordered pair of consecutive rim indices determines its center
when the circumference is at least five. -/
theorem rimIndex_pair_injective {N i j : ℕ}
    (hN : 5 ≤ N) (hi : i < N) (hj : j < N)
    (hpair : s(rimPrevIndex N i, rimNextIndex N i) =
      s(rimPrevIndex N j, rimNextIndex N j)) : i = j := by
  rcases Sym2.eq_iff.mp hpair with ⟨hprev, hnext⟩ | ⟨hcross₁, hcross₂⟩
  · rw [rimNextIndex_eq hi, rimNextIndex_eq hj] at hnext
    split_ifs at hnext <;> omega
  · rw [rimPrevIndex_eq (by omega) hi, rimNextIndex_eq hj] at hcross₁
    rw [rimNextIndex_eq hi, rimPrevIndex_eq (by omega) hj] at hcross₂
    split_ifs at hcross₁ hcross₂ <;> omega

open SimpleGraph

/-- On a simple cycle of length at least five, the unordered pair of
rim neighbors uniquely determines the vertex's canonical position. -/
theorem cycle_rim_neighbors_injective
    {V : Type*} {G : SimpleGraph V} {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hN : 5 ≤ C.length) {i j : ℕ}
    (hi : i < C.length) (hj : j < C.length)
    (hpair : s(C.getVert ((i + C.length - 1) % C.length),
        C.getVert ((i + 1) % C.length)) =
      s(C.getVert ((j + C.length - 1) % C.length),
        C.getVert ((j + 1) % C.length))) : i = j := by
  have hpos : 0 < C.length := by omega
  have hinj {r s : ℕ} (hr : r < C.length) (hs : s < C.length)
      (hrs : C.getVert r = C.getVert s) : r = s :=
    hC.getVert_injOn' (by change r ≤ C.length - 1; omega)
      (by change s ≤ C.length - 1; omega) hrs
  apply rimIndex_pair_injective hN hi hj
  apply Sym2.eq_iff.mpr
  rcases Sym2.eq_iff.mp hpair with ⟨hprev, hnext⟩ | ⟨hcross₁, hcross₂⟩
  · exact Or.inl ⟨hinj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hprev,
      hinj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hnext⟩
  · exact Or.inr ⟨hinj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hcross₁,
      hinj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hcross₂⟩

end JSP000078
