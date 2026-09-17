> Historical snapshot: this document originally described the finite package at e5fff3632957cbd00dec7029b5756a256c263d93. The current full-scope revision supersedes its finite-only exclusions; see [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) and [README.md](README.md). Earlier claims and verification results remain dated evidence, not results for the new revision.

# Complete historical proof architecture

## Structural theorem

Assume a finite vertex-2-connected graph has exactly k≥1 odd cycle lengths and minimum degree at least 2k+1. Choose a longest odd cycle C.

If the complement of C is independent, the proved Lemma 5 forces every selected outside-neighbor set to fill C, shows there is exactly one outside vertex, and concludes completeness with order 2k+2.

Otherwise choose a nontrivial longest path P in that complement. Every endpoint neighbor lies on C or P; an absent neighbor would extend the path. If an endpoint has no C-neighbor, its path spokes yield an exact incident-chord fan. The fan is either rich in odd lengths, all shorter than C, or bipartite with k+1 same-parity paths. Clean linking paths turn the latter family into k+1 odd cycles. Both alternatives contradict the k-length count.

Both endpoints therefore attach to C. Orient P so its first endpoint has no more cycle neighbors than its last. Decompose each degree into the cycle neighbors, proper path chords, and initial path edge. Lemma 4's actual path/cycle constructions give the count, and the exceptional cases reduce to the proved Lemmas 6–8. The equal-singleton neighborhood case is handled separately by a shared fan; Lemma 4 is never applied to an empty erased attachment set. All branches contradict the existence of the outside edge. Thus the complement is independent, finishing the structural theorem.

## Lemma 6 and singleton completion

The endpoint-chord classification distinguishes genuine distinct chords from the case in which both are the edge AB. The shared-edge case uses the triangle and longer connector lengths. The distinct-chord case for k≥2 uses parity-normalized marked distances, connector classes, and a realized minimum odd gap.

For k=1, an odd outside path gives two unequal odd cycle lengths through a proper chord. For an even outside path, deleting the unique common attachment supplies a clean connector to a one-chord fan. The fan is bipartite under the one-odd-length hypothesis. Two paths from Lemma 3, a fixed connector, and the appropriate arc of C produce two unequal odd lengths.

The general singleton endpoint branch uses a strengthened comparison for odd cycles whose supports intersect C in at most one vertex. Deleting that shared vertex and splicing complementary arcs proves the outside odd cycle is shorter. The fan's k odd lengths then omit C.length; its bipartite branch again gives k+1 lengths. Every asserted path or cycle carries an IsPath or IsCycle proof and support/length equations.

## Historical structural-to-coloring consequence

Induct on the finite number of vertices. A graph with at most 2k+2 vertices is trivially colorable with that many colors. If it has no odd cycle, an independent odd-closed-walk argument gives a bipartition.

In the vertex-2-connected case, a vertex of degree below 2k+2 can be removed; induction colors the remainder and an unused color extends it. If no such vertex exists, applying the proved structural theorem at the actual odd-length count gives order at most 2k+2, contradicting the large-order case.

If the graph is not vertex-2-connected, cover it by two proper induced pieces with no cross edges and overlap of at most one vertex. Induction colors both pieces. Permuting colors to match the common vertex allows the colorings to be glued.

`HistoricalColoring.colorable_of_structural_theorem` expresses this implication with an explicit structural premise. **Main supplies the proved `historicalGyarfasStructuralTheorem`**, so the premise is discharged. `FiniteGraphTransport` then transfers finite models through graph isomorphisms to arbitrary vertex universes.

## Dependency independence and sharpness

The 151-module local closure of Main excludes the original DFS modules Coloring, DepthFirst, Parity, and OddCycles. Those files remain as an alternative independently compiled proof, but the final numerical result is justified through the historical route. Main also does not import Sharpness.

Sharpness follows from the complete graph's exact chromatic number, the proved numerical bound, and the arithmetic upper bound of k possible odd lengths between three and 2k+2. There is no circular use of the sharpness theorem in Main.
