# Statement correspondence

## English

Erdős's 1971 original, §7 p.99, asks for orientations with no directed circuit and no circuit becoming directed after one edge reversal. The explicit girth-greater-than-four question appears again in 1976, §8 p.175.

Nešetřil and Rödl, *On a probabilistic graph-theoretical method*, Proceedings AMS 72 (1978), 417–421, Corollary 3 (p.419), proves an ordered-cycle obstruction in every vertex order. Corollary 4 (pp.419–420) produces graphs with no cycles of length <s that are not subgraphs of Hasse diagrams. Taking **s=5** excludes C3 and C4. The solution publication year is **1978**; a 2025 rediscovery or database update is not its publication date.

| Definition | Meaning | Source |
|---|---|---|
| `NoShortCycles 5 G` | Every Mathlib `Walk.IsCycle` has length ≥5 | [Cycles](proof/JSP000838/Cycles.lean) |
| `IsOrientation G D` | `G.Adj u v ↔ D u v ∨ D v u` for every pair, plus asymmetry | [Defs](proof/JSP000838/Defs.lean) |
| `Acyclic D` | No nonempty `Relation.TransGen D v v` | [Defs](proof/JSP000838/Defs.lean) |
| `reverseEdge D u v` | Delete exactly u→v and add exactly v→u | [Orientation](proof/JSP000838/Orientation.lean) |
| `IsRobustAcyclicOrientation` | Exact orientation, initial acyclicity, acyclicity after reversal of every D-edge | [Defs](proof/JSP000838/Defs.lean) |
| `IsCoverGraph G` | A poset on the same vertices whose undirected Hasse graph equals G | [HasseBridge](proof/JSP000838/HasseBridge.lean) |

`NoShortCycles.no_C3_copy` and `.no_C4_copy` exclude arbitrary subgraph copies, not merely induced cycles. The final theorem quantifies over every orientation relation. A topological ranking forces the ordered C5's path and shortcut forward; reversal of the shortcut creates a directed cycle. The exact reversal and Hasse implications are proved, not cited as assumptions.

This is a submitter's statement-comparison guide, not an issued curator-signed statement.

## References

- Erdős (1971), *Some unsolved problems in graph theory and combinatorial analysis*, 97–109: [original paper](https://www.renyi.hu/~p_erdos/1971-25.pdf).
- Erdős (1976), *Problems and results in graph theory and combinatorial analysis*, §8 p.175: [original paper](https://www.renyi.hu/~p_erdos/1976-36.pdf).
- Nešetřil–Rödl (1978): [DOI 10.1090/S0002-9939-1978-0507350-7](https://doi.org/10.1090/S0002-9939-1978-0507350-7).
- Bohman–Frieze–Ruszinkó–Thoma (2000), *A Note on Sparse Random Graphs and Cover Graphs*, EJC 7, R19, p.2 definitions: [EMIS](https://www.maths.tcd.ie/EMIS/journals/EJC/Volume_7/PDF/v7i1r19.pdf).
