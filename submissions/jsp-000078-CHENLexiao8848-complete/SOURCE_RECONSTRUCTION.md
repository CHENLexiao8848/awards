> Historical snapshot: this document originally described the finite package at e5fff3632957cbd00dec7029b5756a256c263d93. The current full-scope revision supersedes its finite-only exclusions; see [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) and [README.md](README.md). Earlier claims and verification results remain dated evidence, not results for the new revision.

# Transparent source reconstruction and completed boundary arguments

The final theorem and constants follow Gyárfás (1992). Formalization required explicit replacements for compressed or potentially misleading intermediate arguments. These local repairs preserve the source-context statements; they are not claims that no other formalization has addressed similar issues.

1. **Lemma 4 complementary lengths.** With outside-route length u, cycle length N, and arc length t, the actual mixed cycle lengths are u+t+2 and u+(N−t)+2. Both contain two attachment edges. When the cycle-side route already has length t+2, its complement requires a +4 offset in the subtraction formula. Explicit cycle constructors avoid the printed intermediate off-by-two count and preserve the endpoint bound.
2. **Empty attachment set.** After excluding one shared neighbor, the selected set can be empty in the singleton case. The final proof handles that case separately with a shared fan, instead of applying the nonempty Lemma 4 count.
3. **Shared AB chord.** The apparent chord at each endpoint can be the same endpoint edge. SharedEdgeException proves that boundary separately rather than silently treating the chords as distinct.
4. **Lemma 6 at k=1.** The omitted source details are filled by the odd-path shortcut and even shared-cycle fan constructions, including a clean connector in a vertex deletion and exact parity/length comparisons.
5. **Lemma 8 orientation.** The original choice of the smaller endpoint neighborhood is retained. The weaker isolated statement with only one arbitrary second-endpoint neighbor is not substituted for it.
6. **Lemma 8 repeated-mark self-pair.** A family interpreted to include a marked point paired with itself would count a nonsimple closed walk. The final proof uses near-saturation one-hub rigidity for k≥2 and a separate k=1 pair-of-neighbors argument. Only actual IsCycle witnesses are counted.
7. **Lemma 5 closure.** The abbreviated gap argument is reconstructed as modular closure by two on an odd cycle. Parity saturation is derived from cycle witnesses before circumference and completeness are concluded.
8. **Two disjoint links.** A shortest-stem two-arm rerouting proof supplies the required clean vertex-disjoint paths without importing Menger as an unproved premise.

The related finite proof incorporated in #130 already includes a structural theorem and some corrected boundary arguments. This submission's originality request concerns its independently implemented complete route, exact standalone rigidity/attachment interfaces, and documented source reconstruction. No unsupported exclusivity claim is made for all repairs.
