# Big-record verification, job bigcheck-7b

Branch `claude/bigcheck-7b-haar-verify-bfxz02`. Verification only: nothing was searched, no checker code was edited, and no VALID verdict was written by hand. Each report holds the machine line, the file's sha256, the full stdout of the reference checker, then the full stdout of the independent checker. Each file's sol file was copied from its branch with `git show` into `research/frontier/sols/`, and each report was committed and pushed with it after its checks finished.

## Results

9 of the 11 files are VALID under both checkers. 2 files (d11D10 and d15D9) are VALID under the independent checker only, because their reference checker does not fit in memory here. Under the two-checker rule they do not qualify for harvest.

Wall time and peak RAM are per checker process (`getrusage` of the child). Machine: 4 cores, 15 GiB RAM, one checker at a time, each checker single-threaded.

| # | file | vertices | cell | reference checker | ref verdict | ref wall / peak RAM | independent checker | ind verdict | ind wall / peak RAM | outcome |
|---:|---|---:|---|---|---|---|---|---|---|---|
| 1 | `d14D9_sl_107_49_orb3_s1` | 120,043,728 | Δ14·D9 | haarcheck_sl | VALID | 46 s / 45 MiB | haarcheck2 | VALID | 48 s / 30 MiB | both VALID |
| 2 | `d20D8_psl_71_343_orb3_s1` | 122,739,120 | Δ20·D8 | haarcheck_psl | VALID | 94 s / 46 MiB | check_haar_indep.py | VALID | 193 s / 3.39 GiB | both VALID |
| 3 | `d9D11_psl_197_19_orb3_s4` | 145,258,344 | Δ9·D11 | haarcheck_psl | VALID | 66 s / 54 MiB | check_haar_indep.py | VALID | 166 s / 3.92 GiB | both VALID |
| 4 | `d11D10_psl_243_11_orb10_frob1d_ar3_s201` | 157,835,304 | Δ11·D10 | build_haar2.py (not run) | NOT RUN (does not fit) | not run | check_haar_indep.py | VALID | 259 s / 4.65 GiB | single checker only (VALID); no reference result |
| 5 | `d15D9_prod_sl_5_sl_19_127_orb3f0_s52` | 208,483,200 | Δ15·D9 | build_haar2.py (not run) | NOT RUN (does not fit) | not run | check_haar_indep.py | VALID | 254 s / 5.58 GiB | single checker only (VALID); no reference result |
| 6 | `d12D10_sl_157_43_orb3f0_s4` | 332,797,296 | Δ12·D10 | haarcheck_sl | VALID | 119 s / 121 MiB | haarcheck2 | VALID | 122 s / 81 MiB | both VALID |
| 7 | `d16D9_sl_101_169_orb3_s1` | 348,207,600 | Δ16·D9 | haarcheck_sl | VALID | 145 s / 126 MiB | haarcheck2 | VALID | 136 s / 85 MiB | both VALID |
| 8 | `d10D11_sl_193_31_orb3_s1` | 445,709,568 | Δ10·D11 | haarcheck_sl | VALID | 142 s / 161 MiB | haarcheck2 | VALID | 144 s / 108 MiB | both VALID |
| 9 | `d17D9_psl_101_487_orb3_s2` | 501,707,400 | Δ17·D9 | haarcheck_psl | VALID | 355 s / 181 MiB | check_haar_indep.py | VALID | 855 s / 13.25 GiB | both VALID |
| 10 | `d13D10_sl_137_133_orb3_ORBW3_s2` | 683,943,456 | Δ13·D10 | haarcheck_sl | VALID | 261 s / 246 MiB | haarcheck2 | VALID | 251 s / 165 MiB | both VALID |
| 11 | `d18D9_sl_127_193_orb3_s2` | 790,626,816 | Δ18·D9 | haarcheck_sl | VALID | 367 s / 284 MiB | haarcheck2 | VALID | 334 s / 190 MiB | both VALID |


sha256 of each sol file (also in line 2 of its report):

- `d14D9_sl_107_49_orb3_s1`: `c801569a4a333b1d6411d83dcf286e2d0cf2da3da5ed02d7e6e46c047786dea3`
- `d20D8_psl_71_343_orb3_s1`: `a6232df43acd68424cf903179f60224ac426629c475a92a5bd3f37c64554556d`
- `d9D11_psl_197_19_orb3_s4`: `6c4df0e6bfe290fa41029c1fe93da12c1205a1c98d8d4dbfbc3fa55d0dd0d473`
- `d11D10_psl_243_11_orb10_frob1d_ar3_s201`: `ffdc15c632d5b9dd1d79150388ef8959640c8f991bc381678504efd0a70cabf1`
- `d15D9_prod_sl_5_sl_19_127_orb3f0_s52`: `2ec69cb54c41c25367a0c2baa57040cf2ac63cd3f92bbeea9215f7a3dc234fc6`
- `d12D10_sl_157_43_orb3f0_s4`: `9e06bacec2e19db03f73d95d618798d8ff765cdbe921aaf1f635b855245593d8`
- `d16D9_sl_101_169_orb3_s1`: `c76302bdb8d10b0edbdeb2c92a7f53130b67e4ec301b7938ffa038ef4cf1ddf9`
- `d10D11_sl_193_31_orb3_s1`: `88c28bc1a5846a56d7c365fc8c90ac939136c30a5b474476ce8c8b167472cfd7`
- `d17D9_psl_101_487_orb3_s2`: `0b27e448484d730813a695a2e662226587a6760a358dcf3fec966a609bc525fc`
- `d13D10_sl_137_133_orb3_ORBW3_s2`: `e8e386e1d5594bac367ae139f973d9e8716c7b475dcec737412b0d3cb5aa4f6f`
- `d18D9_sl_127_193_orb3_s2`: `f2c39be76936da9631c491f4b54100ea18ba4cba578b50caea0e42775e8c47c8`

## Checkers

- Reference, `sl` files: `haarcheck_sl` (from `research/frontier/haarcheck_sl.c`, gcc -O3).
- Reference, `psl` files: `haarcheck_psl` (from `research/structured/tools/haarcheck_psl.c`, gcc -O3).
- Independent, `sl` files: `haarcheck2` (from `research/frontier/haarcheck2.c`, gcc -O3). It has no OpenMP path, so it is single-threaded.
- Independent, `psl`, `prod` and poly-field files: `check_haar_indep.py` (run as `python3 -I`, numpy 2.5.3).
- Reference, poly-field and `prod` files: `build_haar2.py` would be the only reference. It was not run, for the memory reason below.

Every checker was built from master (`8774968`). Each checker ran alone on the machine; the calibration runs below were the only other checks, and they ran one at a time too.

## Did not fit: no reference result

- **d11D10_psl_243_11_orb10_frob1d_ar3_s201** (157,835,304 vertices, GF(3^5) with poly `x^5+2x+1`). The only reference that reads poly fields is `build_haar2.py`. Calibration puts it at about 108 B/vertex (2.32 GB peak at 21.4M vertices), so about 17 GB here. `haarcheck_psl` needs a prime `p` and does not apply. The independent check was VALID (259 s, 4.65 GiB).
- **d15D9_prod_sl_5_sl_19_127_orb3f0_s52** (208,483,200 vertices, `prod sl 5 × sl 19 × Z_127`). `build_haar2.py` would need about 22 GB. `haarcheck_sl` and `haarcheck2` do not read `prod` headers. The independent check was VALID (254 s, 5.58 GiB).

Neither file has a two-checker result, so neither is ready for harvest.

## Calibration (not committed)

Run on master files of about 21M vertices, to set the memory and time estimates before the big runs. All VALID.

| checker | file | vertices | wall | peak RAM |
|---|---|---:|---:|---:|
| haarcheck_psl | d9D10_psl_277_1_s111 | 21,253,656 | 9.7 s | 13 MiB |
| check_haar_indep.py | d9D10_psl_277_1_s111 | 21,253,656 | 160 s | 1.32 GiB |
| build_haar2.py | d9D10_prod_sl_13_sl_17_1_s111 | 21,385,728 | 283 s | 2.27 GiB |
| check_haar_indep.py | d9D10_prod_sl_13_sl_17_1_s111 | 21,385,728 | 5.5 s | 1.04 GiB |
| build_haar2.py | d7D10_psl_49_19_orb3_s1 (poly x^2+1) | 2,234,400 | 5.6 s | 329 MiB |
| check_haar_indep.py | d7D10_psl_49_19_orb3_s1 (poly x^2+1) | 2,234,400 | 1.4 s | 99 MiB |

`check_haar_indep.py` peak memory is not linear in the vertex count: 1.32 GiB at 21M, 3.39 GiB at 123M, 13.25 GiB at 502M. The 502M-vertex run was the largest run here, and it left about 1.7 GiB headroom.

## Notes

- `d17D9_psl_101_487_orb3_s2` was first run in the queue with the independent check marked "not run", on the basis of a linear memory estimate from calibration (about 32 GB). The measured peak was 13.25 GiB, so I reran the independent check. The report on the branch is the rerun. The reference result was rerun unchanged (VALID; 355 s in the rerun, 361 s in the first pass; 181 MiB both times).
- The `sl` checks finished in minutes each (the largest, `d18D9`, took about 6 min for the reference and about 6 min for `haarcheck2`).

## Caveats

- **Shared conventions.** All checkers read the same solution-file format (`d D sl|psl|prod p n NCYC N NTOT`, then `mat(a,b,c,d) z=`), and `check_haar_indep.py` and `haarcheck2` each build their own group arithmetic and indexing. A shared misreading of a file convention would not be caught. Same caveat as the earlier bigcheck jobs.
- **Two-checker rule.** d11D10 and d15D9 do not meet it.
- **Memory margin.** d17D9's independent check used 13.25 GiB of 15 GiB. It would fail on a machine with less RAM.
