# lean-all handoff (worker B, Haiku, Oct 25)

Branch: local `claude/lean-all-B-haiku`, pushed to the session's designated branch `claude/lean-all-haiku-b-hy83he`.

## Scope
STATUS.md lists the 41 records in README.md's table without a Lean ✓, in table order. Worker A has rows 1–21, worker B
rows 22–41. Records are not edited in README.md, RESULTS.md or the records themselves.

## Toolchain
- elan installed to ~/.elan (leanprover/lean4:v4.34.1, same as lean/lean-toolchain). `lake exe cache get` for Mathlib.
- Lean build of one module at a time (lake build BipartiteDD.Haar.<Module>); the machine has 4 cores and 15 GB RAM.

## Where things stand
- Nothing proved yet by worker B at the time of writing; see STATUS.md for the claim.
- Smallest record in B's half: (6,8) 31,680 = Haar graph of PSL(2,11) × Z24 (|G| = 15,840) with the sol file
  research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt. The pattern to copy is lean/BipartiteDD/Haar/D8D8b (PSL(2,17) × Z49,
  the same stage/cover layout, generator in research/lean-haarD/d8D8b/gen_d8D8b.py) and Haar/D6D8-style Diam8 lemma.
- The rest of B's half is at least 2.2M vertices. Stage-by-stage `decide +kernel` (as in D8D8b, about 3.5 codes per group
  element, ~1 min per 2448-code stage) scales linearly with |G|: (11,8) would be ~1,400 stages. Those need a family
  argument (finite geometry / orbit families) rather than per-group certificates; not started.

## Next steps
1. (6,8) 31,680: build PSL(2,11) numbering, generators, covering certificates (words of length ≤ 4 AA/BB, ≤ 3 AB),
   Record module, Axioms check (propext, Classical.choice, Quot.sound only; no sorry/admit/native_decide).
2. Re-check with research/frontier/build_haar2.py and an independent BFS before recording anything.
3. Then decide on the finite-geometry and large Haar rows of B's half (family theorems), updating STATUS.md first.
