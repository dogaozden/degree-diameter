# lean-all handoff (worker B, Haiku, Oct 25)

Branch: local `claude/lean-all-B-haiku`, pushed to the session's designated branch `claude/lean-all-haiku-b-hy83he`.

## Scope
STATUS.md lists the 41 records in README.md's table without a Lean ✓, in table order. Worker A has rows 1–21, worker B
rows 22–41. Records are not edited in README.md, RESULTS.md or the records themselves.

## Toolchain
- elan installed to ~/.elan (leanprover/lean4:v4.34.1, same as lean/lean-toolchain); `lake exe cache get` for Mathlib (ok).
- Build one module at a time with `lake build BipartiteDD.Haar.<Module>` (4 cores, 15 GB RAM). A stage (1584 codes)
  takes about 45 s.

## Done
- Row 22, (6,8) 31,680: `nb_6_8_31680` in `lean/BipartiteDD/Haar/D6D8P11/`. Haar graph of PSL(2,11) × Z24
  (|G| = 15,840, |S| = 6), set from `research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`.
  - Generator: `research/lean-haarD/d6D8psl11/gen_d6D8psl11.py` (copy of the D8D8b generator with p = 11, Z24, six
    generators, base-6 digits). Regenerate with
    `python3 -I research/lean-haarD/d6D8psl11/gen_d6D8psl11.py research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt 1584 lean/BipartiteDD/Haar/D6D8P11`.
  - Stages: `CertAA0..9`, `CertAB0..9`, `CertBB0..9` (10 stages each, one `decide +kernel` per stage). All built.
  - Diameter-8 lemma: `Haar.D7D8.Diam8` (shared). Axioms: `lean/BipartiteDD/Haar/D6D8P11/Axioms.out.txt`
    shows `[propext, Classical.choice, Quot.sound]`. Banned-token scan is empty.
  - Independent check: `research/frontier/build_haar2.py` on the sol file: n = 31680, degree 6, ecc 8 from both sides, VALID.

## Blocked (rest of B's half)
- Every other row in B's half is a Haar or finite-geometry graph with at least 2.2M vertices. The per-element certificate
  used for (6,8) costs about 28 ms per code and 3·order(G) codes per Haar record. For (11,8) that is about 26 h of kernel
  time on one core; the largest row is about 15,000 h. These rows need a family argument, not a bigger certificate.
- Finite-geometry rows (13,8), (8,9), (7,10), (8,10): not started; the family theorem for those constructions is not in lean/.

## Next steps (if continued)
1. Ask the coordinator whether a per-group certificate of about 26 h (single core, parallel builds maybe 7 h) is worth it
   for (11,8) alone, or whether the family route is preferred.
2. Look for a family-level covering argument for the orbit-search Haar rows; check STATUS.md before claiming.
3. Finite-geometry rows: read the existing lean/BipartiteDD/GQST and SingerC files for a general statement first.
