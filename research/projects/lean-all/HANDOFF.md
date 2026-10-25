# lean-all handoff (worker A)

Read first: `research/projects/lean-all/BRIEF.md`, then `STATUS.md` in this folder (the claimed rows and their status).

## State

- Branch: `claude/lean-all-a-haiku-ymy6nl` (the session's designated branch; the brief's `claude/lean-all-A-haiku` name was not used).
- Worker A owns rows 1–20 of `STATUS.md`; worker B owns rows 21–41.
- No `HANDOFF.md` existed on `master` or on the earlier `origin/lean-all` branch when this session started. This file is new.

## Toolchain in this cloud session (no Mathlib cache)

- `elan` cannot install in this sandbox: its self-update check calls the GitHub API and fails with "failed to parse latest release tag". The toolchain was installed by hand:
  - `https://releases.lean-lang.org/lean4/v4.34.1/lean-4.34.1-linux.tar.zst` (reachable), extracted with the `zstandard` Python package into `~/.elan/toolchains/leanprover--lean4---v4.34.1/`.
  - Put `~/.elan/toolchains/leanprover--lean4---v4.34.1/bin` first on `PATH`. `lean --version` gives 4.34.1 and `lake --version` works.
- The Mathlib cache host `cache.leanprover-community.org` is refused by the egress proxy (CONNECT 502, not on this session's allowed list). `lake exe cache get` cannot work here. Mathlib is therefore compiled from source. `git ls-remote` to GitHub works, so the Mathlib source clones.
- Build of `BipartiteDD` needs about 750 Mathlib modules first. Compile it in the background and do not start the whole default target: it includes every heavy record module. Build only the module you touch, e.g. `lake build BipartiteDD.Haar.D4D7.Record`.

## Notes on the first record (4,7) = 864

- The construction is in `research/theorems/smallfam/graphs/build_d4D7_n864.py`: Haar graph of `G = Heis(F_9) ⋊ C_16` (SmallGroup(432,233)) with `S` of 4 elements. Two other 864-vertex candidates (SmallGroup(432,247), (432,249)) are in the same folder.
- The Lean route is the D=7 lemma `BipartiteDD.Haar.haar_isBipartiteDegDiam7_of_equiv` (`lean/BipartiteDD/Haar/Diam7.lean`), which needs both six-letter covers over `G`. The pattern to copy is `lean/BipartiteDD/Haar/D5D7b/` (record 3120): `Group`, `Words`, `Check` (certificate tables), `Stage*`, `Cover`, `Record`, `Axioms`.
- Metacyclic `Z_m ⋊_r Z_n` (all 432-order options) gave no valid covering `S` in a random and hill-climb search (best 849 of 864 in the A/B words). A search over `Z_3^3 ⋊_M Z_16` (M in GL(3,3) with M^16 = I) is in progress; see below.
