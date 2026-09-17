import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

/-!
# JSP-000562: a strict valley in fourth-prime-factor densities

Natural density here means the limit of the actual counting function on `(0,N]`.
Finite signed sums of divisibility indicators are used as an inclusion-exclusion
certificate.  Their densities follow from the exact count `N / d` of multiples
of `d`; no independence assumption or unverified numerical evaluation is used.
-/

namespace JSP000562

open Filter Finset
open scoped Topology

/-- The natural density of a predicate on positive integers. -/
def HasNaturalDensity (P : ℕ → Prop) [DecidablePred P] (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (((Ioc 0 N).filter P).card : ℝ) / N) atTop (𝓝 d)

/-- The prime `p` is the fourth smallest *distinct* prime dividing `n`. -/
def IsFourthPrimeFactor (p n : ℕ) : Prop :=
  p.Prime ∧ p ∣ n ∧ ((range p).filter (fun q => q.Prime ∧ q ∣ n)).card = 3

instance (p : ℕ) : DecidablePred (IsFourthPrimeFactor p) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- This definition uses the actual finite set of distinct prime factors. -/
theorem isFourthPrimeFactor_iff_primeFactors (p n : ℕ) (hn : n ≠ 0) :
    IsFourthPrimeFactor p n ↔
      p ∈ n.primeFactors ∧ (n.primeFactors.filter (· < p)).card = 3 := by
  have he : (range p).filter (fun q => q.Prime ∧ q ∣ n) =
      n.primeFactors.filter (· < p) := by
    ext q
    simp only [mem_filter, mem_range, Nat.mem_primeFactors_of_ne_zero hn]
    tauto
  simp [IsFourthPrimeFactor, he, Nat.mem_primeFactors_of_ne_zero hn, and_assoc]

abbrev Term := ℤ × ℕ

def evalTerms (ts : List Term) (n : ℕ) : ℝ :=
  (ts.map (fun t => (t.1 : ℝ) * if t.2 ∣ n then 1 else 0)).sum

def densityTerms (ts : List Term) : ℚ :=
  (ts.map (fun t => (t.1 : ℚ) / t.2)).sum

def restrictTerms (p : ℕ) (ts : List Term) : List Term :=
  ts.map (fun t => (t.1, Nat.lcm p t.2))

def negateTerms (ts : List Term) : List Term :=
  ts.map (fun t => (-t.1, t.2))

@[simp] theorem evalTerms_nil (n : ℕ) : evalTerms [] n = 0 := rfl

@[simp] theorem evalTerms_cons (t : Term) (ts : List Term) (n : ℕ) :
    evalTerms (t :: ts) n = (t.1 : ℝ) * (if t.2 ∣ n then 1 else 0) + evalTerms ts n := rfl

@[simp] theorem evalTerms_append (ts us : List Term) (n : ℕ) :
    evalTerms (ts ++ us) n = evalTerms ts n + evalTerms us n := by
  simp [evalTerms]

@[simp] theorem evalTerms_negate (ts : List Term) (n : ℕ) :
    evalTerms (negateTerms ts) n = -evalTerms ts n := by
  induction ts with
  | nil => simp [negateTerms]
  | cons t ts ih =>
    change ((-t.1 : ℤ) : ℝ) * (if t.2 ∣ n then 1 else 0) +
      evalTerms (negateTerms ts) n = -((t.1 : ℝ) * (if t.2 ∣ n then 1 else 0) + evalTerms ts n)
    rw [ih, Int.cast_neg]
    ring

@[simp] theorem evalTerms_restrict (p : ℕ) (ts : List Term) (n : ℕ) :
    evalTerms (restrictTerms p ts) n = (if p ∣ n then 1 else 0) * evalTerms ts n := by
  induction ts with
  | nil => simp [restrictTerms]
  | cons t ts ih =>
    change (t.1 : ℝ) * (if Nat.lcm p t.2 ∣ n then 1 else 0) +
      evalTerms (restrictTerms p ts) n = _
    rw [ih]
    by_cases hp : p ∣ n <;> by_cases ht : t.2 ∣ n <;>
      simp [Nat.lcm_dvd_iff, hp, ht]

/-- Inclusion-exclusion certificate for exactly `r` divisors among the list `ps`. -/
def exactlyTerms : List ℕ → ℕ → List Term
  | [], 0 => [(1, 1)]
  | [], _ + 1 => []
  | p :: ps, 0 => exactlyTerms ps 0 ++ negateTerms (restrictTerms p (exactlyTerms ps 0))
  | p :: ps, r + 1 =>
      exactlyTerms ps (r + 1) ++ negateTerms (restrictTerms p (exactlyTerms ps (r + 1))) ++
        restrictTerms p (exactlyTerms ps r)

theorem eval_exactlyTerms (ps : List ℕ) (r n : ℕ) :
    evalTerms (exactlyTerms ps r) n =
      if ps.countP (fun p => p ∣ n) = r then 1 else 0 := by
  induction ps generalizing r with
  | nil => cases r <;> simp [exactlyTerms, evalTerms]
  | cons p ps ih =>
    cases r with
    | zero =>
      by_cases h : p ∣ n <;> simp [exactlyTerms, ih, h]
    | succ r =>
      by_cases h : p ∣ n <;> simp [exactlyTerms, ih, h]

theorem tendsto_div_count (d : ℕ) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / N) atTop (𝓝 (1 / (d : ℝ))) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ)
    (a := 1 / (d : ℝ)) (by positivity)).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_natCast,
    Nat.floor_natCast] using h

theorem sum_evalTerms (ts : List Term) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, evalTerms ts n =
      (ts.map (fun t => (t.1 : ℝ) * (N / t.2 : ℕ))).sum := by
  induction ts with
  | nil => simp [evalTerms]
  | cons t ts ih =>
    simp only [evalTerms_cons, sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [← mul_sum]
    congr 1
    simp [← Nat.Ioc_filter_dvd_card_eq_div, sum_boole]

theorem tendsto_evalTerms (ts : List Term) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, evalTerms ts n) / N)
      atTop (𝓝 (densityTerms ts : ℝ)) := by
  simp only [sum_evalTerms]
  induction ts with
  | nil => simp [densityTerms]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, add_div]
    have ht := (tendsto_div_count t.2).const_mul (t.1 : ℝ)
    convert ht.add ih using 1 <;> simp [densityTerms, div_eq_mul_inv, mul_assoc]

theorem hasNaturalDensity_of_terms (P : ℕ → Prop) [DecidablePred P]
    (ts : List Term) (h : ∀ n, evalTerms ts n = if P n then 1 else 0) :
    HasNaturalDensity P (densityTerms ts : ℝ) := by
  have hs (N : ℕ) : (∑ n ∈ Ioc 0 N, evalTerms ts n) =
      (((Ioc 0 N).filter P).card : ℝ) := by simp [h, sum_boole]
  simpa only [HasNaturalDensity, hs] using tendsto_evalTerms ts

def fourthTerms (p : ℕ) (ps : List ℕ) : List Term :=
  restrictTerms p (exactlyTerms ps 3)

theorem fourth_density_of_list (p : ℕ) (ps : List ℕ)
    (hp : p.Prime) (hn : ps.Nodup)
    (hs : ps.toFinset = (range p).filter Nat.Prime) :
    HasNaturalDensity (IsFourthPrimeFactor p) (densityTerms (fourthTerms p ps) : ℝ) := by
  apply hasNaturalDensity_of_terms
  intro n
  have hc : ((range p).filter (fun q => q.Prime ∧ q ∣ n)).card =
      ps.countP (fun q => q ∣ n) := by
    rw [← filter_filter, ← hs]
    exact hn.card_eq_countP
  simp only [fourthTerms, evalTerms_restrict, eval_exactlyTerms, IsFourthPrimeFactor, hp,
    true_and, hc]
  by_cases hd : p ∣ n <;> by_cases hc' : ps.countP (fun q => q ∣ n) = 3 <;> simp [hd, hc']

def primesBelow13 : List ℕ := [2, 3, 5, 7, 11]
def primesBelow17 : List ℕ := [2, 3, 5, 7, 11, 13]
def primesBelow19 : List ℕ := [2, 3, 5, 7, 11, 13, 17]

theorem density_fourth_13 :
    HasNaturalDensity (IsFourthPrimeFactor 13) (31 / 5005) := by
  have h := fourth_density_of_list 13 primesBelow13 (by decide) (by decide) (by decide)
  have hc : densityTerms (fourthTerms 13 primesBelow13) = 31 / 5005 := by decide +kernel
  simpa only [hc, Rat.cast_div, Rat.cast_ofNat] using h

theorem density_fourth_17 :
    HasNaturalDensity (IsFourthPrimeFactor 17) (206 / 36465) := by
  have h := fourth_density_of_list 17 primesBelow17 (by decide) (by decide) (by decide)
  have hc : densityTerms (fourthTerms 17 primesBelow17) = 206 / 36465 := by decide +kernel
  simpa only [hc, Rat.cast_div, Rat.cast_ofNat] using h

theorem density_fourth_19 :
    HasNaturalDensity (IsFourthPrimeFactor 19) (1308 / 230945) := by
  have h := fourth_density_of_list 19 primesBelow19 (by decide) (by decide) (by decide)
  have hc : densityTerms (fourthTerms 19 primesBelow19) = 1308 / 230945 := by decide +kernel
  simpa only [hc, Rat.cast_div, Rat.cast_ofNat] using h

/-- A prime-indexed sequence increases up to a mode, then decreases. -/
def PrimeUnimodal (d : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → d p ≤ d q) ∧
    (∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → d q ≤ d p)

/-- Any assignment of the actual fourth-prime-factor densities has a strict valley. -/
theorem fourth_density_not_unimodal (d : ℕ → ℝ)
    (hd : ∀ p, p.Prime → HasNaturalDensity (IsFourthPrimeFactor p) (d p)) :
    ¬ PrimeUnimodal d := by
  have h13 : d 13 = 31 / 5005 := tendsto_nhds_unique (hd 13 (by decide)) density_fourth_13
  have h17 : d 17 = 206 / 36465 := tendsto_nhds_unique (hd 17 (by decide)) density_fourth_17
  have h19 : d 19 = 1308 / 230945 := tendsto_nhds_unique (hd 19 (by decide)) density_fourth_19
  rintro ⟨m, hleft, hright⟩
  by_cases hm : 17 ≤ m
  · have h := hleft 13 17 (by decide) (by decide) (by omega) hm
    rw [h13, h17] at h
    norm_num at h
  · have h := hright 17 19 (by decide) (by decide) (by omega) (by omega)
    rw [h17, h19] at h
    norm_num at h

/-- A defined sequence of the genuine natural densities, for every prime. -/
noncomputable def fourthDensity (p : ℕ) : ℝ :=
  densityTerms (fourthTerms p (((range p).filter Nat.Prime).sort (· ≤ ·)))

theorem fourthDensity_is_density (p : ℕ) (hp : p.Prime) :
    HasNaturalDensity (IsFourthPrimeFactor p) (fourthDensity p) :=
  fourth_density_of_list p _ hp (sort_nodup _ _) (sort_toFinset _ _)

theorem fourthDensity_values :
    fourthDensity 13 = 31 / 5005 ∧
      fourthDensity 17 = 206 / 36465 ∧ fourthDensity 19 = 1308 / 230945 := by
  exact ⟨tendsto_nhds_unique (fourthDensity_is_density 13 (by decide)) density_fourth_13,
    tendsto_nhds_unique (fourthDensity_is_density 17 (by decide)) density_fourth_17,
    tendsto_nhds_unique (fourthDensity_is_density 19 (by decide)) density_fourth_19⟩

theorem fourthDensity_strict_valley :
    fourthDensity 17 < fourthDensity 13 ∧ fourthDensity 17 < fourthDensity 19 := by
  obtain ⟨h13, h17, h19⟩ := fourthDensity_values
  rw [h13, h17, h19]
  norm_num

/-- JSP-000562: the density sequence for `k = 4` is not unimodal. -/
theorem jsp000562 : ¬ PrimeUnimodal fourthDensity :=
  fourth_density_not_unimodal fourthDensity fourthDensity_is_density

end JSP000562
