> Historical snapshot: this document originally described the finite package at e5fff3632957cbd00dec7029b5756a256c263d93. The current full-scope revision supersedes its finite-only exclusions; see [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) and [README.md](README.md). Earlier claims and verification results remain dated evidence, not results for the new revision.

# Prize, originality, and contribution-priority claims

## Requested assessment

The submitter affirmatively requests Justin Sun Prize assessment for this **completed independent Lean formalization**, its complete historical structural route, and its precise reusable structural results. Please evaluate actual formalization contributions, statement fidelity, independent implementation, proof reconstruction, and verification evidence, and record a reasoned decision on eligibility and attribution.

The claim is for the submitted formalization and proof architecture. The original mathematical discovery belongs to Gyárfás (1992), following the Bollobás-Erdős problem and Gallai's stronger structural formulation.

## Completed contribution beyond the prior snapshots

PR #517 recorded the independent finite DFS bound, universal sharpness, and initial historical linking/Lemma 1 work. PR #581 added historical Lemmas 2, 3, 4, 5, 7, and 8 and standalone rigidity/boundary results. This submission closes the remaining proof obligations and connects the entire historical route to Main.

New completed work includes:

1. The equal-neighbor one-chord exception for all k, including shared endpoint edges and the k=1 even-path connectivity case.
2. The previously delicate singleton common-neighbor branch, using a fan that meets the longest odd cycle in at most one vertex.
3. The complete longest-cycle/longest-outside-path endpoint reduction and Gyárfás structural Theorem 1.
4. An independent odd-closed-walk bipartite base, vertex deletion color extension, and separator recoloring/gluing.
5. A vertex-count coloring induction whose structural premise is supplied by the actual structural theorem, followed by finite-model universe transport.

The final Main theorem no longer relies on the earlier DFS numerical proof. Its recursive local import closure is supplied as evidence. This change is the principal reason the completed submission merits a distinct review from the earlier snapshots.

## Specific standalone originality claims for assessment

The package also puts forward the following independently proved interfaces:

- Outside-hub rigidity: for k≥2, one outside vertex with 2k selected neighbors on an odd cycle and exactly k odd lengths forces circumference 2k+1, without longestness, degree, independent-complement, or connectivity premises.
- Two-large-attachment obstruction: an outside nonempty simple path cannot have at least 2k selected attachments at each endpoint when exactly k odd lengths occur, without global degree/maximality assumptions.
- Shared-single-attachment criterion: 2k attachments at one endpoint and one shared selected attachment at the other already force k+1 odd lengths.
- Shared-endpoint-edge and singleton boundary completions with explicit clean-path/simple-cycle witnesses.

These claims identify concrete formal implementation and theorem-interface contributions for assessment. The inspected related packages already contain a DFS proof, a finite structural theorem, and some source-boundary repairs. The general theorem, DFS idea, and every correction are therefore not presented as exclusively discovered here. The bounded comparison does not purport to be an exhaustive search of all literature.

## Priority and preservation of the record

The submitter requests recognition of priority **for each specific contribution to the extent established by immutable evidence**, and retains the claim to appropriate originality, attribution, and prize recognition.

| Public record | What it establishes |
| --- | --- |
| Related #130, opened 2026-09-16 15:50:58 UTC | Earlier related submission; its recorded chronology is acknowledged |
| Related #458, opened 2026-09-17 04:17:27 UTC | Additional related arbitrary-graph/reproduction contribution |
| Own #517, opened 2026-09-17 06:18:35 UTC, commit d172a837ba1bd1849b9dc9f8e6c6ad088085fcfb | Priority record for the work actually disclosed in that snapshot |
| Own #581, opened 2026-09-17 07:51:20 UTC, commit e024cd78379a2a61942d2593ca576c39b2a53d7e | Priority record for the added structural library actually disclosed there |
| This completed submission and release | Timestamp and immutable source for the final historical integration |

Newly completed work is not backdated to older snapshots. There is no blanket waiver of priority, originality, attribution, or eligibility, and no unsupported claim to an earlier global completion date. Please compare the actual independent implementation and final exports when assessing the contribution. Both earlier PRs remain unchanged.
