import Mathlib.Data.List.Chain
import Mathlib.Algebra.Ring.Parity

namespace JSP000078

/-- In a list whose Boolean labels alternate, the label at index `i`
differs from the initial label exactly when `i` is odd. -/
theorem alternating_getElem_ne_iff_odd {A : Type*} (p : A → Bool) :
    ∀ (l : List A) (a : A),
      (a :: l).IsChain (fun x y => p x ≠ p y) →
      ∀ (i : ℕ) (hi : i < (a :: l).length),
        p ((a :: l)[i]) ≠ p a ↔ Odd i := by
  intro l
  induction l with
  | nil =>
      intro a hc i hi
      have hz : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
      subst i
      simp
  | cons b l ih =>
      intro a hc i hi
      cases i with
      | zero => simp
      | succ i =>
          have hrest : i < (b :: l).length := Nat.lt_of_succ_lt_succ hi
          have hab : p a ≠ p b := (List.isChain_cons_cons.mp hc).1
          have htail : (b :: l).IsChain (fun x y => p x ≠ p y) :=
            (List.isChain_cons_cons.mp hc).2
          have hindex := ih b htail i hrest
          have hflip : (p ((b :: l)[i]) ≠ p a) ↔
              ¬ (p ((b :: l)[i]) ≠ p b) := by
            cases hpa : p a <;> cases hpb : p b <;>
              cases hpi : p ((b :: l)[i]) <;> simp_all
          simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one, Nat.odd_add_one]
            using hflip.trans (not_congr hindex)

/-- A vertex whose Boolean label differs from the head of an alternating
list has an odd index. -/
theorem odd_index_of_alternating {A : Type*} (p : A → Bool) {l : List A}
    (hc : l.IsChain (fun a b => p a ≠ p b)) (hne : l ≠ [])
    (i : Fin l.length) (hi : p l[i] ≠ p (l.head hne)) : Odd i.val := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a l =>
      exact (alternating_getElem_ne_iff_odd p l a hc i.val i.isLt).mp hi

end JSP000078
