# Evidence-based comparison with PR #130 and PR #517

## Compared records

- Related submission: [PR #130](https://github.com/TheJustinSunPrize/awards/pull/130), pinned head `524c5971113fb0405e90534e5709093de7b43f3f`.
- Its declared finite-proof source: [plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e), commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- Submitter's earlier package: [PR #517](https://github.com/TheJustinSunPrize/awards/pull/517), commit `d172a837ba1bd1849b9dc9f8e6c6ad088085fcfb`.

The comparison retrieved the 42 Lean files listed in #130's diff at that pinned revision, including proof and verification utilities. Their source inventories and byte hashes were checked, and the principal DFS, fan, structural, independent-complement, and boundary modules were inspected. They were downloaded to a separate read-only comparison area and are not copied into this submission. This comparison is not a re-verification of #130's build or a criticism of its soundness.

## Actual coverage and architecture

| Topic | PR #130 / its incorporated finite proof | This submission |
| --- | --- | --- |
| Finite numerical bound | Present, including DFSUpper with a normal-tree construction | Independently implemented stack induction with a colored/uncolored boundary invariant |
| Arbitrary infinite vertex types | General.lean extends via compactness | Finite vertex types; no infinite extension is asserted |
| Full structural theorem and equality characterization | Structural.gyarfas_structural and General.erdos_58 are present | Seven historical lemmas and standalone structural results; full global assembly remains outside this snapshot |
| Incident-chord counting and paths | Fan and Structural/FanApplication contain actual geometric constructions, parity counts, and arbitrary endpoint path families | Exact CycleWithIncidentChords representation; geometric witnesses and standalone exports for Lemmas 2 and 3 |
| Endpoint count | EndpointCount and Structural/EndpointApplication contain count and geometric bridges | Explicit complementary attachment lengths and arbitrary selected-neighbor endpoint theorem |
| Distinct-neighbor boundary | Structural/BoundaryApplication.differentNeighborhoodNoChordBoundary explicitly retains endpoint orientation and repairs the boundary | Separate one-hub rigidity theorem for k≥2 and two-endpoint obstruction, with an independent k=1 proof |
| Source proof completeness | Incorporated finite structural proof is present | General Lemma 6 and final global structural assembly remain to be completed |
| Toolchain | Lean/Mathlib 4.33.0 in the pinned related package | Lean/Mathlib 4.34.0 |

The related work already contains a DFS approach, a structural proof, path constructors, and source-boundary repairs. Those facts rule out presenting these general themes as absent from all prior submissions. The requested contribution assessment instead focuses on the precise independently implemented theorem interfaces and the stronger standalone hypotheses in CLAIMS.md.

## Specific comparison anchors

- Prior finite bound: `ErdosProblems/Erdos58/DFSUpper.lean`, especially `NormalTree`, `exists_normalTree_of_connected`, and `colorable_of_oddCycleLengths_card_le`.
- Prior structural completion: `ErdosProblems/Erdos58/Structural.lean`, `gyarfas_structural_twoConnected` and `gyarfas_structural`.
- Prior distinct-neighbor repair: `ErdosProblems/Erdos58/Structural/BoundaryApplication.lean`, `differentNeighborhoodNoChordBoundary`; its documentation explicitly identifies the endpoint orientation.
- Prior independent-complement rigidity: `Structural/IndependentGap.lean` uses the inherited degree/odd-length/exterior context. Our `odd_cycle_length_eq_of_outside_hub` is exported for a single outside hub with 2k selected neighbors, without those global premises.

No exact matching standalone outside-hub or two-large-attachment theorem interface was identified in this bounded source review. This is evidence for a specific comparison request, not proof of global mathematical novelty. All proof bodies of the compared file sets have different byte hashes; byte difference alone is not evidence of mathematical novelty.

## Increment beyond the submitter's own #517

The imported mathematical library has 85 new Lean modules, two modified entry/audit modules, and 22 unchanged modules relative to #517. New checked exports include historical Lemmas 2, 3, 4, 5, 7, and 8; one-hub rigidity; the strengthened attachment obstruction; and the shared-endpoint-edge exception. The old proof and old PR remain preserved. The new PR uses a distinct directory and branch, so it can be reviewed or merged without overwriting #517.
