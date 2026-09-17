import JSP000078.CycleTwoArcLengths
import JSP000078.FanRectanglePaths
import JSP000078.TriplePathCounting

/-!
# Two different path lengths from an internal spoke

The exceptional small counting case needs just two path lengths. The ordinary
cycle arcs already suffice unless they have equal lengths. In that case the
two routes through an internal spoke cannot both have that same length.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A spoke strictly between two nonbase cycle positions supplies two
simple paths between them with different lengths. No parity hypothesis is needed. -/
theorem exists_two_fan_paths_of_internal_spoke {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {r t s : ℕ} (hr : 1 ≤ r) (hrt : r < t) (hts : t < s)
    (hs : s < C.length) (hat : G.Adj c (C.getVert t)) :
    ∃ P : Fin 2 → G.Walk (C.getVert r) (C.getVert s),
      (∀ i, (P i).IsPath) ∧ Function.Injective (fun i ↦ (P i).length) := by
  obtain ⟨p, q, hp, hq, hplen, hqlen⟩ :=
    exists_cycle_two_arcs_with_lengths hC (by omega : r < s) hs
  by_cases hpq : p.length ≠ q.length
  · exact exists_two_paths_of_length_ne p q hp hq hpq
  have hequal : p.length = q.length := not_ne_iff.mp hpq
  have ha₁ : G.Adj c (C.getVert 1) := C.adj_snd hC.not_nil
  have haLast : G.Adj c (C.getVert (C.length - 1)) :=
    (C.adj_penultimate hC.not_nil).symm
  obtain ⟨a, ha, halen⟩ := exists_fan_path_LM hC (by omega : 1 ≤ 1) hr hrt hts hs ha₁ hat
  obtain ⟨b, hb, hblen⟩ := exists_fan_path_MR hC hr hrt hts
    (by omega : s ≤ C.length - 1) (by omega : C.length - 1 < C.length) hat haLast
  by_cases hpa : p.length ≠ a.length
  · exact exists_two_paths_of_length_ne p a hp ha hpa
  apply exists_two_paths_of_length_ne p b hp hb
  intro hpb
  have hpaEq : p.length = a.length := not_ne_iff.mp hpa
  omega

end JSP000078
