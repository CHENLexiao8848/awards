# Proof guide

## English

The proof specializes the 1978 ordered-template method to five-cycles and replaces its probabilistic carrier with a finite greedy construction.

1. **Carrier:** N=2^96, d=2^20, M=120·96·N. Build M five-sets, each vertex used at most d times, avoiding pairs joined by at most three previous shadow steps. Saturated vertices and forbidden neighborhoods each occupy less than N/2. See [FiniteSeparation](proof/JSP000838/FiniteSeparation.lean) and [Carrier](proof/JSP000838/Carrier.lean).
2. **Pasting:** any relabelled C5 per block preserves absence of C3/C4. Eight triangle and sixteen quadrilateral old/new edge patterns yield a forbidden old short path. See [Gluing](proof/JSP000838/Gluing.lean), [LocalCycle](proof/JSP000838/LocalCycle.lean), [Pasting](proof/JSP000838/Pasting.lean).
3. **All orders:** each block has 120 permutation labels. At most 119 labels miss its prescribed monotone cycle for a fixed rank. At most N^N ranks exist; N^N·119^M<120^M guarantees one assignment successful for every rank. Duplicate labels producing the same graph are harmless. See [FiniteChoice](proof/JSP000838/FiniteChoice.lean) and [SourceTheorem](proof/JSP000838/SourceTheorem.lean).
4. **Obstruction:** a topological ranking makes the ordered C5 a directed four-edge path plus forward shortcut. Reversing the shortcut creates a cycle. Cover arrows give the Hasse contradiction, including arbitrary subgraph copies in infinite posets. See [OrderedObstruction](proof/JSP000838/OrderedObstruction.lean), [HasseBridge](proof/JSP000838/HasseBridge.lean), [CoverObstruction](proof/JSP000838/CoverObstruction.lean).

[Main](proof/JSP000838/Main.lean) assembles the existential counterexample and explicit conjecture negation. N is generous, not minimal. Fixed C5 facts use kernel `decide`; no external graph computation is trusted. The axiom audit covers construction and final theorems.
