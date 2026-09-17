# Attribution and licensing

## English

**Mathematical result:** Jaroslav Nešetřil and Vojtěch Rödl (1978), with the original question recorded by Erdős and associated with Ore. See [references](STATEMENT.md).

**Submitted contribution:** complete Lean 4 formalization, an internally proved finite deterministic carrier for s=5, exact reversal/Hasse bridges, reproducibility tooling and an English review guide. The submitter used OpenAI Codex with AI assistance. No claim is made of exclusively manual authorship, independent human verification, first discovery of the negative result, or priority over all unpublished formalizations.

**Recipient attribution:** `RECIPIENT-jsp-000838-A` denotes the submitter's formalization contribution pending the recipient-confirmation process. GitHub history records the submitting account. No unconfirmed legal identity, private contact, payment arrangement or attestation is published. The submitter has a direct interest in recognition and is not an independent verifier.

New Lean sources and `proof/verify.py` use the [MIT license](proof/LICENSE). Submission prose follows the repository's [CC BY 4.0 license](../../LICENSE-CONTENT). Mathlib remains an external pinned dependency with its own Apache 2.0 license and author credits. No paper PDFs, extracted text or downloaded dependency sources are included.

## Existing formal evidence

During pre-submission duplicate checking, [issue #24](https://github.com/TheJustinSunPrize/awards/issues/24) was found to register an existing formal proof of this problem: [`Erdos1006.not_erdos_1006` at pinned commit 8822f7d](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1006.lean). That issue reports reproduction using Lean 4.33.0. Its formalization attribution remains with the contributors documented by that source.

The present submission is a separately developed, self-contained Lean 4.34.0 development in the `JSP000838` namespace, with a finite greedy carrier, explicit Hasse/subgraph bridges and its own source/audit history. It is submitted for assessment of that contribution, not as the first known Lean proof or a replacement for the earlier contributors' credit. Reviewers should compare both pinned sources when evaluating novelty, attribution and eligibility.
