import JSP000078.PathGluing

/-!
# Support and endpoint contacts after splitting a path

The two-link rerouting argument splits a simple path at a newly reached
vertex. These facts preserve disjointness and the endpoint-only contact
conditions for the resulting prefix and suffix.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- The prefix and suffix of a simple path intersect only at their shared
splitting vertex. -/
theorem support_intersection_takeUntil_dropUntil {t b y : V} {p : G.Walk t b}
    (hp : p.IsPath) (hy : y ∈ p.support) :
    ∀ v ∈ (p.takeUntil y hy).support, v ∈ (p.dropUntil y hy).support → v = y := by
  have hsplit : ((p.takeUntil y hy).append (p.dropUntil y hy)).IsPath := by
    simpa only [Walk.take_spec] using hp
  intro v hvp hvq
  by_contra hvy
  exact hsplit.ne_of_mem_support_of_append hvy hvp hvq rfl

/-- A suffix beginning strictly after the start of a simple path avoids
the original initial vertex. -/
theorem path_start_notMem_support_dropUntil {t b y : V} {p : G.Walk t b}
    (hp : p.IsPath) (hy : y ∈ p.support) (hyt : y ≠ t) :
    t ∉ (p.dropUntil y hy).support := by
  intro ht
  exact hyt (support_intersection_takeUntil_dropUntil hp hy t
    (p.takeUntil y hy).start_mem_support ht).symm

/-- If a path meets a set only at its final vertex, every prefix meets the
set only at the prefix's own final vertex (or does not meet it at all). -/
theorem path_takeUntil_end_contact {t b y : V} {p : G.Walk t b} {B : Set V}
    (hp : p.IsPath) (hy : y ∈ p.support)
    (hB : ∀ v ∈ p.support, v ∈ B → v = b) :
    ∀ v ∈ (p.takeUntil y hy).support, v ∈ B → v = y := by
  intro v hv hvB
  have hvb := hB v (p.support_takeUntil_subset_support hy hv) hvB
  subst v
  by_contra hby
  exact Walk.endpoint_notMem_support_takeUntil hp hy hby hv

omit [DecidableEq V] in
/-- A path with a later splitting vertex has distinct original endpoints. -/
theorem path_start_ne_end_of_split {t b y : V} {p : G.Walk t b}
    (hp : p.IsPath) (hy : y ∈ p.support) (hyt : y ≠ t) : t ≠ b := by
  intro htb
  have hnil : p.Nil := hp.nil_iff_eq.mpr htb
  have hsupport : p.support = [t] := Walk.nil_iff_support_eq.mp hnil
  exact hyt (by simpa only [hsupport, List.mem_singleton] using hy)

omit [DecidableEq V] in
/-- The initial vertex is outside an endpoint-contact set whenever the
path contains a vertex other than that initial vertex. -/
theorem path_start_notMem_of_end_contact {t b y : V} {p : G.Walk t b} {B : Set V}
    (hp : p.IsPath) (hy : y ∈ p.support) (hyt : y ≠ t)
    (hB : ∀ v ∈ p.support, v ∈ B → v = b) : t ∉ B := by
  intro htB
  exact path_start_ne_end_of_split hp hy hyt (hB t p.start_mem_support htB)

end JSP000078
