# JSP-000838: complete Lean 4 negative solution

## English

This submission proves the negative answer to [Erdős Problem 1006](https://www.erdosproblems.com/1006), catalogued as [JSP-000838](../../problems/catalog-0801-0900.md#JSP-000838): there exists a finite simple graph without triangles or four-cycles for which no orientation is acyclic and remains acyclic after every single-edge reversal.

**Review status:** submitter-run Lean kernel checks pass. Independent mathematical review, the prize's signed statement and verification process, recipient confirmation and eligibility assessment are requested, not represented as completed. The mathematical negative answer is due to Nešetřil and Rödl (1978).

## Formal result

[Main.lean](proof/JSP000838/Main.lean) proves:

```lean
JSP000838.jsp_000838_counterexample :
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    JSP000838.NoShortCycles 5 G ∧
      ∀ D, ¬ JSP000838.IsRobustAcyclicOrientation G D

JSP000838.jsp_000838_conjecture_false :
  ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    JSP000838.NoShortCycles 5 G →
      ∃ D, JSP000838.IsRobustAcyclicOrientation G D)
```

There is no unproved source-theorem premise. The graph on `Fin (2^96)` is established symbolically; no adjacency list of that size is generated. The code also proves the s=5 Hasse-diagram arbitrary-subgraph obstruction, including infinite ambient posets. The all-girth generalization is outside scope; s=5 fully answers the catalog question.

## Reproduce

Install Elan from its official distribution, then run:

```shell
cd submissions/jsp-000838/proof
lake exe cache get
python3 verify.py --clean --output-dir ../evidence
```

Preserve `lake-manifest.json`; do not run `lake update` for reproduction. Lean is pinned to **4.34.0**, Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`. Dependency caches are permitted. `--clean` removes only this project's build directory and recompiles its sources; it is not an isolated two-checker run.

The verifier checks actual toolchain and Mathlib HEAD, all 18 Lean files, all nine axiom reports, and unchanged source hashes. A failed rerun invalidates an earlier success. Audited declarations use only `propext`, `Classical.choice`, `Quot.sound`.

- [Verification summary](evidence/summary.json)
- [Build log](evidence/build.txt)
- [Axiom audit](evidence/axioms.txt)
- [Statement comparison](STATEMENT.md)
- [Proof guide](PROOF_GUIDE.md)
- [Attribution and licenses](ATTRIBUTION.md)
- [Requested review](REVIEW.md)

The containing full commit SHA pins the proof and evidence. Paper PDFs and unrelated workspace files are excluded. Lean sources have an explicit [MIT license](proof/LICENSE); submission prose follows the repository's [CC BY 4.0 license](../../LICENSE-CONTENT).
