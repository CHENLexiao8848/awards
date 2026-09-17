# Proof and dependency structure

## Numerical theorem

Let k count the distinct odd simple-cycle lengths. Use colors in Bool × Fin (k+1). Maintain an uncolored finite set, a simple path stack with alternating first color coordinates, a proper coloring of already colored vertices, and the invariant that every edge from an uncolored to a colored vertex ends on the stack.

When a new vertex x extends the stack, choose its first coordinate opposite to the stack head. A neighboring stack vertex with that coordinate has odd index i. The stack prefix and its edge to x form a simple odd cycle of length i+2. Distinct indices give distinct lengths, so there are at most k conflicting vertices and forbidden second coordinates. One of k+1 second coordinates remains.

Push the newly colored vertex when possible. If the head has no uncolored neighbor, pop it; the boundary invariant persists. When the stack is empty, start from another uncolored vertex. Every transition decreases 2 * uncolored.card + stack.length, so strong induction produces a coloring of every vertex, including across components. The palette has 2k+2 colors.

Dependencies, all proved in this package:

1. Basic: exact finite cycle-length set and length bound.
2. OddCycles: path prefixes closed by chords and injective length count.
3. Parity: alternating Boolean labels and odd indices.
4. DepthFirst: finite path-extension coloring principle with all invariants.
5. Coloring: local extension rule and spare color.
6. Main: proper coloring, chromatic conclusion, exact-k and zero cases.
7. Sharpness: odd lengths inject into the k available odd integers; complete-graph chromatic number and Main force equality. This is not circular: Main does not import Sharpness.

## Additional historical proof progress

JSP000078.historicalCycleLinking proves two vertex-disjoint clean links between disjoint cycles in a 2-connected graph. It uses a shortest-stem two-arm construction, vertex deletion, path trimming, and rerouting. No Menger theorem is added as an assumption.

JSP000078.outside_odd_cycle_length_lt_longest in GyarfasLemmaOne.lean formalizes Gyárfás's Lemma 1, printed pages 42-43: an odd cycle vertex-disjoint from a longest odd cycle is strictly shorter. Complementary arcs and two links yield two odd cycles with total length |C|+|D|+2(|P|+|Q|); maximality gives the contradiction.

HistoricalSpec contains definitions, not assumed truths; its linking obligation is discharged by HistoricalLinking. Gyárfás Lemmas 2-8 and his stronger structural theorem are not claimed here. The numerical theorem uses the independent depth-first proof, which is not attributed to either supplied paper.
