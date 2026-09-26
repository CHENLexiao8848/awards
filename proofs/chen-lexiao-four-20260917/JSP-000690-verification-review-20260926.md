# JSP-000690 — two-version verification evidence, 2026-09-26

This report supports the consolidated review in [PR #747](https://github.com/TheJustinSunPrize/awards/pull/747) while preserving the earlier public [PR #737](https://github.com/TheJustinSunPrize/awards/pull/737). These are two implementations of the same known construction, not two independent prize claims. **No new Lean compilation or replay was performed for this review.** The two terminals share a name, `JSP000690.solution`, but their imports and statements differ; each result below is tied to its own fixed source.

## A: primary explicit proper-subhypergraph implementation

Repository `CHENLexiao8848/awards`, branch `codex/four-lean-proofs-20260917`, proof commit **`ea6e7fc0a5893edd13335acc4e1ebd00cd261782`**, package `proofs/chen-lexiao-four-20260917/proof`.

- [Fixed `Problems/JSP000690.lean`](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000690.lean): 11,586 bytes, SHA256 `1aa1dd02054f94bf906c7029c6c4fe52381c55d1d68d2668f4f14719ffca2411`.
- [Verification report](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/report.json), [fixed verifier](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verify.py) and [checksum manifest](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/SHA256SUMS).
- [Build transcript](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/build.log), [public axiom audit](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/axioms.log), [module replay transcript](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/kernel-replay.log), and [audit source](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Audit.lean).

All 61 package Git blobs, 18 before/after input hashes, 41 logged command hashes/arguments/exit codes, 60 checksum entries and nine dependency revisions/clean tracked statuses before and after were rechecked successfully. The historical report records a successful arm64 macOS run on 2026-09-17 from 09:48:38 to 09:55:31 UTC using Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. It explicitly ran `lake clean pinnacleLean` and built eight local package modules in 2,055 jobs, retaining dependency caches. It audited 11 declarations and replayed eight modules across the four-problem package.

The JSP000690-specific evidence is **one** terminal audit, `JSP000690.solution`, with exactly `[propext, Classical.choice, Quot.sound]`, plus actual build and replay of `Problems.JSP000690`. The helper `every_proper_subgraph_two_colorable` has its signature printed by `#check`; it has no separate `#print axioms` output in that audit. It is used in the final terminal's definition of `IsThreeColorCritical`.

The final result supplies a finite hypergraph with nine vertices and 22 distinct edges, every edge of size three, exact chromatic number three, minimum degree exactly seven, and two-colorability of every proper subhypergraph with vertices and/or edges removed. The submitted implementation proves the structural extension from finite deletion certificates explicitly. This does not establish a first formalization or a new mathematical construction.

These are submitter-provided historical execution logs, not a Lean CI run or independent execution today. The three GitHub workflows inspected at this proof SHA concern catalog validation and data, not compilation of this proof. To reproduce, run `python3 verify.py` in the fixed package; the verifier's default protocol includes the local-library clean, build, audits and local-module replay.

## B: earlier PR implementation and exact-SHA Linux CI

Repository `CHENLexiao8848/jsp-000637-lean`, branch `codex/lean5-completed-20260917`, proof commit **`060945b90e39e6ce77731e31879d83075309bee5`**, package `batches/lean5`.

- [Fixed `LeanTwenty/JSP000690.lean`](https://github.com/CHENLexiao8848/jsp-000637-lean/blob/060945b90e39e6ce77731e31879d83075309bee5/batches/lean5/LeanTwenty/JSP000690.lean): 6,307 bytes, SHA256 `9dea96349e7f72d78b456d7273cdb03c8d46208aa23c60ef0a79ac6ee5a52795`.
- [Verifier](https://github.com/CHENLexiao8848/jsp-000637-lean/blob/060945b90e39e6ce77731e31879d83075309bee5/batches/lean5/scripts/verify.py), [source lock](https://github.com/CHENLexiao8848/jsp-000637-lean/blob/060945b90e39e6ce77731e31879d83075309bee5/batches/lean5/source-lock.json) and [workflow](https://github.com/CHENLexiao8848/jsp-000637-lean/blob/060945b90e39e6ce77731e31879d83075309bee5/.github/workflows/lean5.yml).
- [Run 35226287772](https://github.com/CHENLexiao8848/jsp-000637-lean/actions/runs/35226287772), dedicated [job 105218613127](https://github.com/CHENLexiao8848/jsp-000637-lean/actions/runs/35226287772/job/105218613127): successful at the exact B proof SHA.
- Artifact `10500050565`, `lean5-JSP-000690`: 6,162 ZIP bytes, SHA256 `edbbdbd0fba0d042ee095cf24372ae4c6bdc47b8f81c0368b6e6db5ed221683b`, matching GitHub's digest. Its recorded expiry is 2026-12-16T13:18:54Z.

ZIP integrity, all seven extracted members and 14 selected fixed Git blobs were checked. All 27 CI source records match the fixed source lock. Six relevant available inputs were independently rehashed: entry, toolchain, lakefile, dependency manifest, proof metadata and upstream lock. The other 21 batch records were compared to the lock only, not all independently fetched. This report does not audit the other nine problems in the batch.

The actual job used a fresh hosted Ubuntu checkout without project cache restoration or tracked oleans, while downloading pinned dependency caches. It reports `Built LeanTwenty.JSP000690 (125s)` and a successful 3,092-job build. All nine dependency checkouts match their manifest pins. The actual Lean 4.34.0 toolchain is x86_64 Linux, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; Mathlib has the same pin as A. This is fresh-project compilation with cached dependencies, without an explicit `lake clean`.

The generated audit imports `LeanTwenty.JSP000690` and prints the sole terminal `JSP000690.solution`, with exactly `[propext, Classical.choice, Quot.sound]`. All five recorded commands exited zero, including entry replay. The terminal constructs an edge family over `Fin 9`, proves three-uniformity, minimum degree exactly seven, three-colorability/non-two-colorability, and every single-edge/single-vertex deletion two-colorable. A's all-proper-subhypergraph predicate and explicit edge-count conjunct are not part of B's final signature. B's single-deletion certificates support the usual criticality interpretation; they should be retained as valid earlier evidence rather than called an invalid proof.

To reproduce B, run `python scripts/verify.py --problem JSP-000690 --fetch-cache` from its fixed package. The command builds and audits B only. The verifier checks its source lock before and after, then replays `LeanTwenty.JSP000690`; these results must not be assigned to A's differently defined theorem of the same name.

## Transparent corrections to B's historical metadata

The fixed `proofs.json` convenience field lists an obsolete source hash `611c3d23d8cefce13634a87fee3d8c953c6b7e6b15c1019d335276e4f97d02fd`. The actual published source, source lock, successful CI and local evidence JSON all give the correct `9dea96349e7f72d78b456d7273cdb03c8d46208aa23c60ef0a79ac6ee5a52795`. A [later immutable supplement](https://github.com/CHENLexiao8848/jsp-000637-lean/blob/a4d83d426d9ee2d92511857831e27b70216aedfe/batches/lean5-additional/evidence/previous-batch-supplement.json) supplies that correction. Its claim that the old value is explained solely by CRLF is not independently established: uniform LF-to-CRLF conversion of the actual published file yields `462aee48d366ec6142ca46398a8de4087eb94fc315c37c974d8a99b6c6497229`, not that old value. The verifier authenticates the actual bytes with the correct `source-lock.json`; it does not rely on this obsolete convenience field.

There is also a mismatch in the older local JSON/log pair: the JSON's `source_log_sha256` is `bb2426ce1450e0f641026a94b8e8f6ee7dbaf8853ed37f160747b921106a2cec`, whereas the adjacent published log is `e4c84ff2894db0619fbc4ad3b5cb498769835c4babf974bcf3b68338f2df5a24` (uniform CRLF conversion gives `c3c6976eb4ff7377bd5a6f8c89d9d424649e28f6f6e4db6bdb0658ad9115f1f3`). That old pair is preserved for history but is not relied on as a consistent hash chain. The exact-SHA GitHub CI artifact below independently supplies the actual successful compilation, terminal audit and replay. No new source execution is claimed for this explanatory correction.

## Shared limitations and preservation

Both replay protocols use Lean's bundled kernel with pinned imported dependencies, not a second independent implementation or `--fresh` verification of every Mathlib dependency. A's replay includes its eight local package modules; B's replay is only its single named entry. Neither package's submitter-controlled evidence constitutes independent human mathematical review, organizer acceptance, or proof of original authorship or award priority. The mathematical construction and earlier complete formalizations must retain their separate attribution.

An auxiliary Python finite-data check during this review agreed with the common nine-vertex, 22-edge list and degree sequence `(10,7,7,7,7,7,7,7,7)`, exhausted all 512 binary colorings, and validated both implementations' 22 edge-deletion colorings and B's nine vertex-deletion colorings. It generated no new certificates and ran no Lean. Certificate-table differences do not establish independent provenance.

A's historical logs are permanently linked at its fixed commit. The following table and six embedded short files preserve B's actual CI artifact before expiry. The cache-download progress log is omitted from the body, with its digest retained. Every embedded file was extracted back from this Markdown and rehashed against the exact ZIP member. The original B verification JSON has no per-log digests; this preservation supplies them, and explicitly records its absent final newline.


| Artifact member | Bytes | SHA256 |
|---|---:|---|
| `Audit.lean` | 62 | `a8d0bab769b1dc5018008de2f29e53ceabb70f6ff4622af35a81c1675c9f1225` |
| `axioms.log` | 80 | `f7ec22b1cd72ee26a9df85244e0e6e82fcf8501048a21ef5dd829cfbdf8ea4bf` |
| `build.log` | 211 | `8410741644a11cd633c6482e085cb11d5c3a3ea29ef9c4add53b1c0c29182d92` |
| `cache.log` | 9963 | `75c7ea88504178e8319dd25cb266c85221f00e3f7802b7236b23b7b87f313213` |
| `kernel.log` | 31 | `7b1871c1fcc999e49b535ea9c413f6168f761882770200b5e6586cd5ee86a4a3` |
| `toolchain.log` | 1669 | `96ce379e441b32899159b48ef33979997d4e25efb235234987ee22a2766820de` |
| `verification.json` | 6361 | `6ec7e5a52093228f3cef4db426d9c4487bac4967e7088ce59483949155397a58` |

## `Audit.lean`

SHA256: `a8d0bab769b1dc5018008de2f29e53ceabb70f6ff4622af35a81c1675c9f1225`; original final newline: `true`.

<!-- BEGIN artifact: Audit.lean -->
```lean
import LeanTwenty.JSP000690

#print axioms JSP000690.solution
```
<!-- END artifact: Audit.lean -->

## `build.log`

SHA256: `8410741644a11cd633c6482e085cb11d5c3a3ea29ef9c4add53b1c0c29182d92`; original final newline: `true`.

<!-- BEGIN artifact: build.log -->
```text
ℹ [3092/3092] Built LeanTwenty.JSP000690 (125s)
info: LeanTwenty/JSP000690.lean:129:0: 'JSP000690.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3092 jobs).
```
<!-- END artifact: build.log -->

## `axioms.log`

SHA256: `f7ec22b1cd72ee26a9df85244e0e6e82fcf8501048a21ef5dd829cfbdf8ea4bf`; original final newline: `true`.

<!-- BEGIN artifact: axioms.log -->
```text
'JSP000690.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```
<!-- END artifact: axioms.log -->

## `kernel.log`

SHA256: `7b1871c1fcc999e49b535ea9c413f6168f761882770200b5e6586cd5ee86a4a3`; original final newline: `true`.

<!-- BEGIN artifact: kernel.log -->
```text
replaying LeanTwenty.JSP000690
```
<!-- END artifact: kernel.log -->

## `toolchain.log`

SHA256: `96ce379e441b32899159b48ef33979997d4e25efb235234987ee22a2766820de`; original final newline: `true`.

<!-- BEGIN artifact: toolchain.log -->
```text
info: downloading https://releases.lean-lang.org/lean4/v4.34.0/lean-4.34.0-linux.tar.zst
info: installing /home/runner/.elan/toolchains/leanprover--lean4---v4.34.0
info: mathlib: cloning https://github.com/leanprover-community/mathlib4.git
info: mathlib: checking out revision '5ed2965256430c3649e86755f9576b54eca72435'
info: plausible: cloning https://github.com/leanprover-community/plausible
info: plausible: checking out revision '118aa17ee84656b8bd727fef7c458ee8c833385c'
info: LeanSearchClient: cloning https://github.com/leanprover-community/LeanSearchClient
info: LeanSearchClient: checking out revision 'ddf04cf3949fa556442341e87d47f9f6e6074707'
info: importGraph: cloning https://github.com/leanprover-community/import-graph
info: importGraph: checking out revision 'e928b72544873815af278d38681b31c0293588e3'
info: proofwidgets: cloning https://github.com/leanprover-community/ProofWidgets4
info: proofwidgets: checking out revision '106ff4fafc74ef4ac99d81dbf3ab399118f497a5'
info: aesop: cloning https://github.com/leanprover-community/aesop
info: aesop: checking out revision '355695d523e41d0554926416cba2a2b3544fbbc9'
info: Qq: cloning https://github.com/leanprover-community/quote4
info: Qq: checking out revision '6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259'
info: batteries: cloning https://github.com/leanprover-community/batteries
info: batteries: checking out revision 'f2effa3d803fda822b1f97b806c47cf2adfbcbc2'
info: Cli: cloning https://github.com/leanprover/lean4-cli
info: Cli: checking out revision 'e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204'
Lean (version 4.34.0, x86_64-unknown-linux-gnu, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)
```
<!-- END artifact: toolchain.log -->

## `verification.json`

SHA256: `6ec7e5a52093228f3cef4db426d9c4487bac4967e7088ce59483949155397a58`; original final newline: `false`.

<!-- BEGIN artifact: verification.json -->
```json
{
  "problem": "JSP-000690",
  "status": "passed",
  "started_utc": "2026-09-17T13:19:08.171349+00:00",
  "theorems": [
    "JSP000690.solution"
  ],
  "allowed_axioms": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "lean": "4.34.0",
  "mathlib_commit": "5ed2965256430c3649e86755f9576b54eca72435",
  "source_hashes": [
    {
      "path": "LeanTwenty/JSP000759.lean",
      "sha256": "8d71bc141d32ce4da7b5637a8cbcdced605d0dbf1d19902367d1b663adbb3247",
      "bytes": 9858
    },
    {
      "path": "LeanTwenty/Problem000746.lean",
      "sha256": "fe741e61ded3523cb4bc0e785475f9ce7e8f41ec24ef6cad45170540042f79ed",
      "bytes": 5730
    },
    {
      "path": "LeanTwenty/JSP000690.lean",
      "sha256": "9dea96349e7f72d78b456d7273cdb03c8d46208aa23c60ef0a79ac6ee5a52795",
      "bytes": 6307
    },
    {
      "path": "LeanTwenty/JSP000897.lean",
      "sha256": "04ec9c946fe06fd0e7ed53b8efa9314577b84bb61eb6a56d5d2c4b794632275b",
      "bytes": 1235
    },
    {
      "path": "LeanTwenty/Upstream/Erdos1079.lean",
      "sha256": "e3aa40e54458784d54a72482a7716be65f582a8691899efe36dde9e3cc07509e",
      "bytes": 18718
    },
    {
      "path": "LeanTwenty/JSP000896.lean",
      "sha256": "b4a7537d1ac2187ebda2f33e6016b27f8197edf0dc6b2845ed989d3020a2a5bb",
      "bytes": 890
    },
    {
      "path": "LeanTwenty/Upstream/Erdos1078.lean",
      "sha256": "79055365caf42f6ec4e3c7ff5bd7863a73af74b2c798951aa516facbdf94130c",
      "bytes": 37800
    },
    {
      "path": "LeanTwenty/JSP000842.lean",
      "sha256": "02dcab35cf9a72a6b4097caa204fe64fa23ef505083c8d8cb06ea09ee5814f97",
      "bytes": 1102
    },
    {
      "path": "LeanTwenty/JSP001021.lean",
      "sha256": "d7e3c477bfb46608db6afecaaa715cd906f8d9319212fd159e95454296234b0f",
      "bytes": 3381
    },
    {
      "path": "LeanTwenty/Upstream/Erdos1216.lean",
      "sha256": "96d70169d8946ed780c9419139bc34cddc38f836c344ae0b47ff28c0a39cc3fa",
      "bytes": 48635
    },
    {
      "path": "LeanTwenty/Upstream/Erdos1216/Certificates.lean",
      "sha256": "da9a1c93e177bc814ef80984c5afed176777547ffcaf449b327023bbd98b27c0",
      "bytes": 3263124
    },
    {
      "path": "LeanTwenty/JSP000653.lean",
      "sha256": "b01200abec3ef792d1cad24e88f46b551a53af5348bd895b07224bc6411d38d9",
      "bytes": 1473
    },
    {
      "path": "LeanTwenty/JSP000733.lean",
      "sha256": "61d6035f89ac432767ef13dd06e3992dad8ae8b658f97872c1981c4348d95d9b",
      "bytes": 10063
    },
    {
      "path": "LeanTwenty/External/Erdos882/Core.lean",
      "sha256": "c00a0906cfe3f0dcb7cc8e7cb968e0711cb39c7b04833d48f289759aa6b83fb6",
      "bytes": 26074
    },
    {
      "path": "LeanTwenty/JSP000725.lean",
      "sha256": "8866113ea9d0bd63f41ff36566251e4285875f8f078152a70714d541afd5b9f0",
      "bytes": 1771
    },
    {
      "path": "LeanTwenty.lean",
      "sha256": "d6c66c86a314af12d73ee96d69f765db5605855c56064651584c957cdde57c4f",
      "bytes": 493
    },
    {
      "path": "lean-toolchain",
      "sha256": "8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632",
      "bytes": 25
    },
    {
      "path": "lake-manifest.json",
      "sha256": "c910a858577ad46005840705bb04421e3c5367f713536472abd07e198a901f97",
      "bytes": 3511
    },
    {
      "path": "LeanTwenty/Certificates/JSP000746.cnf",
      "sha256": "260b7c50fac4fcc4525f7253eb37a8750bf744cff5bb41e92a314cdea1ccab45",
      "bytes": 12986
    },
    {
      "path": "LeanTwenty/Certificates/JSP000746.lrat",
      "sha256": "55172fa9925cb62926d91a078590e9480b294b5c7727e27e8b68858ca20ac20b",
      "bytes": 218957
    },
    {
      "path": "LeanTwenty/External/Erdos882/LICENSE",
      "sha256": "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30",
      "bytes": 11358
    },
    {
      "path": "LeanTwenty/External/Erdos882/NOTICE.md",
      "sha256": "a59d9d37245e18984764dd39d8bbad8caf5ebb85307fa828821664762c83b376",
      "bytes": 503
    },
    {
      "path": "LeanTwenty/Upstream/NOTICE.md",
      "sha256": "d2596184fd29fac17272cfa74c119ac1b9a37a4a280ac7c04e2f199357830f15",
      "bytes": 1141
    },
    {
      "path": "licenses/Apache-2.0.txt",
      "sha256": "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30",
      "bytes": 11358
    },
    {
      "path": "lakefile.toml",
      "sha256": "cde26a663f61ee2593fa768a6d683b797d3b614f7ff48ae393a1bc07b9917be0",
      "bytes": 278
    },
    {
      "path": "proofs.json",
      "sha256": "179941858f184f3a3136d27da40058aae6ce4a6c513cc9c58f0e8fbb62cf0f52",
      "bytes": 7540
    },
    {
      "path": "upstream-lock.json",
      "sha256": "02bd63c567ea09ac03d6a91a47194fb365b108b9a7c6eeefa96ca165559f4720",
      "bytes": 11286
    }
  ],
  "checks": [
    {
      "command": [
        "lake",
        "env",
        "lean",
        "--version"
      ],
      "exit_code": 0,
      "started_utc": "2026-09-17T13:19:08.175887+00:00",
      "ended_utc": "2026-09-17T13:20:07.471249+00:00",
      "log": "toolchain.log"
    },
    {
      "command": [
        "lake",
        "exe",
        "cache",
        "get"
      ],
      "exit_code": 0,
      "started_utc": "2026-09-17T13:20:07.471518+00:00",
      "ended_utc": "2026-09-17T13:21:10.826626+00:00",
      "log": "cache.log"
    },
    {
      "command": [
        "lake",
        "build",
        "LeanTwenty.JSP000690"
      ],
      "exit_code": 0,
      "started_utc": "2026-09-17T13:21:10.859791+00:00",
      "ended_utc": "2026-09-17T13:23:18.802444+00:00",
      "log": "build.log"
    },
    {
      "command": [
        "lake",
        "env",
        "lean",
        "verification/JSP-000690/Audit.lean"
      ],
      "exit_code": 0,
      "started_utc": "2026-09-17T13:23:18.802896+00:00",
      "ended_utc": "2026-09-17T13:23:21.911142+00:00",
      "log": "axioms.log"
    },
    {
      "command": [
        "lake",
        "env",
        "leanchecker",
        "--verbose",
        "LeanTwenty.JSP000690"
      ],
      "exit_code": 0,
      "started_utc": "2026-09-17T13:23:21.911597+00:00",
      "ended_utc": "2026-09-17T13:25:32.231544+00:00",
      "log": "kernel.log"
    }
  ],
  "replay_scope": "Entry module using Lean bundled kernel; imports dependencies, not --fresh",
  "verification_kind": "submitter-run, not independent human review",
  "completed_utc": "2026-09-17T13:25:32.249457+00:00"
}
```
<!-- END artifact: verification.json -->

