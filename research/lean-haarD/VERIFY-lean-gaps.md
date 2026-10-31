# Independent rebuild: lean/BipartiteDD/Haar new proofs (lean-gaps2)

Checker: Haiku verification job "lean-verify". No Lean file was edited.

Checked branch: `claude/lean-gaps2-haar-proofs-9qjlsg` (head `2ec41cf`), which contains
`claude/lean-gaps-proofs-3qf4j2`. Checked out into `claude/verify-lean-haar-proofs-j3b37r`.

## Environment

- Lean 4.34.1 (from `lean/lean-toolchain`), Lake 5.0.0, Mathlib from the cache
  (`lake exe cache get`, 8908 files).
- Machine: 4 cores, 16 GB RAM in a memory cgroup.
- Wall time and peak memory: `/usr/bin/time -v` (GNU time 1.9), "Maximum resident set size" is the peak RSS of the largest single process.

## Results

| # | Folder | Record module | Build | Wall time | Peak RSS | Axioms identical | Theorem statement line |
|---|--------|---------------|-------|-----------|----------|------------------|------------------------|
| 1 | D3D10N810 | `Record.lean` | PASS | 1:20.76 | 6,275,500 kB (5.98 GiB) | yes | `theorem nb_3_10_810 : ∃ G : SimpleGraph (Fin 810), BipartiteDD.IsBipartiteDegDiam G 3 10 :=` |
| 2 | D4D7Heis9C16 | `Record864.lean` | PASS | 0:39.33 | 3,506,520 kB (3.34 GiB) | yes | `theorem nb_4_7_864 : ∃ G : SimpleGraph (Fin 864), BipartiteDD.IsBipartiteDegDiam G 4 7 := by` |
| 3 | D3D11N1344 | `Record.lean` | PASS | 1:47.71 | 10,358,408 kB (9.88 GiB) | yes | `theorem nb_3_11_1344 : ∃ G : SimpleGraph (Fin 1344), BipartiteDD.IsBipartiteDegDiam G 3 11 :=` |
| 4 | D3D12N2368 | `Record.lean` | PASS | 3:12.81 | 4,624,188 kB (4.41 GiB) | yes | `theorem nb_3_12_2368 : ∃ G : SimpleGraph (Fin 2368), BipartiteDD.IsBipartiteDegDiam G 3 12 :=` |
| 5 | D10D5GQ7Z6 | `Record.lean` | PASS (see note A) | 5:34 (serial, sum of 13 steps) | 10,956,104 kB (10.45 GiB), in `Check` | yes | `theorem nb_10_5_n4800 : ∃ G : SimpleGraph (Fin 4800), BipartiteDD.IsBipartiteDegDiam G 10 5 :=` |
| 6 | D11D5GQ8Z6 | `Record.lean` | PASS (see note A) | 11:23 (serial, sum of 15 steps) | 9,945,672 kB (9.49 GiB), in `Local0` | yes | `theorem nb_11_5_n7020 : ∃ G : SimpleGraph (Fin 7020), BipartiteDD.IsBipartiteDegDiam G 11 5 :=` |
| 7 | D8D5N2048 | `Record.lean` | PASS | 1:17.10 | 4,793,968 kB (4.57 GiB) | yes | `theorem nb_8_5_n2048 : ∃ G : SimpleGraph (Fin 2048), BipartiteDD.IsBipartiteDegDiam G 8 5 :=` |
| 8 | D5D8N9760 | `Record9760.lean` | PASS | 0:56.11 | 2,786,476 kB (2.66 GiB) | yes | `theorem nb_5_8_n9760 : ∃ G : SimpleGraph (Fin 9760), BipartiteDD.IsBipartiteDegDiam G 5 8 := by` |
| 9 | D5D9N29756 | `Record29756.lean` | PASS | 1:43.83 | 2,824,648 kB (2.69 GiB) | yes | `theorem nb_5_9_n29756 : ∃ G : SimpleGraph (Fin 29756), BipartiteDD.IsBipartiteDegDiam G 5 9 := by` |
| 10 | D6D8PSL11Z24 | `Record31680.lean` | PASS | 6:29.08 | 4,678,748 kB (4.46 GiB) | yes | `theorem nb_6_8_n31680 : ∃ G : SimpleGraph (Fin 31680), BipartiteDD.IsBipartiteDegDiam G 6 8 := by` |

Axioms: each `lake env lean <Folder>/Axioms.lean` output was compared with the committed `Axioms.out.txt`.
All ten are identical, and each reads `[propext, Classical.choice, Quot.sound]`.

### Notes

A. Rows 5 and 6 failed on the first attempt and were rebuilt. The first attempt ran `lake build`
   with several Lean jobs in parallel. The kernel OOM-killed three `lean` processes
   (exit 137, cgroup OOM in dmesg), so those failures were memory, not proof errors. The rebuild
   used one `lake build <module>` per module in dependency order (one Lean process at a time).
   Every step exited 0 and the axioms matched. Wall times are sums of the serial steps. Some of
   the steps had already built in the failed run, so these sums are a lower bound on the cold build.
   Peak RSS is the maximum over the 13 (row 5) or 15 (row 6) steps. The `Record` step itself
   only peaks at about 1.8 GB, because its dependencies were already built. The largest step is the
   real peak.

B. Rows 1-4 and 7-10 were built with `lake build <Record>`, which runs in parallel by default. Peak
   RSS is still a per-process value. Those builds did not OOM. Their times are cold, with the
   Mathlib cache present.

C. The committed Axioms.out.txt files were not edited.

## Static checks

- `grep -n -w -E "sorry|admit|axiom|native_decide|implemented_by|extern"` over every `.lean` file
  in the ten folders: no matches.
- `git diff --name-status origin/master...HEAD`: 191 entries, all `A` (added). No existing
  file was modified, renamed or deleted. The added files are under `lean/BipartiteDD/Haar/` and
  `research/lean-haarD/`.
