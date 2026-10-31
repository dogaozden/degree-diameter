# Big-record verification, job bigcheck-7a

Branch `claude/bigcheck-7a-haar-verify-5wnild`. Verification only: nothing was searched, no checker code was edited, and no VALID verdict was written by hand. Each report holds the machine line, the file's sha256, the full stdout of the reference checker, then the full stdout of the independent checker. Each sol file was copied from its source branch with `git show` into `research/frontier/sols/`.

## Results

All 9 files are VALID under both checkers.

| vertices | file | reference checker (wall, peak RSS) | independent checker (wall, peak RSS) | verdicts |
|---:|---|---|---|---|
| 8,418,120 | d10D9_psl_59_41_orb5f0_ORBW5RESTART1_s12 | haarcheck_psl: VALID, 3.8 s, 13 MB | check_haar_indep.py: VALID, 5.6 s, 288 MB | VALID / VALID |
| 17,323,152 | d11D9_sl_43_109_orbw3_s3 | haarcheck_sl: VALID, 5.5 s, 13 MB | haarcheck2: VALID, 5.2 s, 13 MB | VALID / VALID |
| 18,666,480 | d15D8_psl_41_271_orb5f0_ORBW5_s1 | haarcheck_psl: VALID, 11.2 s, 13 MB | check_haar_indep.py: VALID, 18.3 s, 578 MB | VALID / VALID |
| 24,099,600 | d9D10_psl_151_7_orb3f0_s1 | haarcheck_psl: VALID, 11.0 s, 13 MB | check_haar_indep.py: VALID, 33.0 s, 787 MB | VALID / VALID |
| 35,445,648 | d12D9_sl_83_31_orb3f0_orbw3_s3 | haarcheck_sl: VALID, 12.2 s, 14 MB | haarcheck2: VALID, 12.3 s, 13 MB | VALID / VALID |
| 41,373,072 | d17D8_sl_53_139_orb3_c15 | haarcheck_sl: VALID, 17.5 s, 16 MB | haarcheck2: VALID, 19.6 s, 13 MB | VALID / VALID |
| 57,637,680 | d18D8_sl_61_127_orb3_s2 | haarcheck_sl: VALID, 25.8 s, 22 MB | haarcheck2: VALID, 32.1 s, 15 MB | VALID / VALID |
| 64,294,560 | d10D10_psl_81_121_orb5f0_s3 (GF(81), `poly x^4+x+2`) | build_haar2.py: VALID, 215.8 s, 3,745 MB | check_haar_indep.py --poly: VALID, 40.6 s, 1,670 MB | VALID / VALID |
| 86,317,296 | d19D8_psl_103_79_orb3_s1 | haarcheck_psl: VALID, 65.3 s, 33 MB | check_haar_indep.py: VALID, 137.1 s, 2,520 MB | VALID / VALID |

Wall times and peak RSS are per checker run, measured by the runner (`getrusage` on the child process). Every run exited with rc=0.

## Method

* Machine: 4 cores, 15 GB RAM, one check at a time.
* Reference checker by family: `haarcheck_sl` for `sl p` files; `haarcheck_psl` for `psl p` files with p prime; `build_haar2.py` for `psl 81 poly x^4+x+2`, because `haarcheck_psl` accepts only prime p.
* Independent checker: `haarcheck2` for `sl` files. `haarcheck2` accepts only `sl` headers, so `check_haar_indep.py` was used for the `psl` files, including the GF(81) file with `--poly x^4+x+2`.
* Checkers were built or taken from master (`git show origin/master:...`) into a scratch directory; the checker sources were not edited.
* Sizes: all headers agree with `N = |G|·n` and `vertices = 2N`, computed by hand for each file (for example d10D9: |PSL(2,59)|·41 = 4,209,060, so 8,418,120 vertices).
* Each report was committed on its own and pushed after its two checks finished. The sol file was committed alongside its report.
* No check was stopped by the 3-hour limit, and none ran out of memory. The largest peak was 3.7 GB (build_haar2.py on the GF(81) file), well inside 15 GB. The brief's estimate of about 10 GB for that file was pessimistic.

## Caveats

* One machine: 4 cores, 15 GB RAM.
* The two checkers for each file read the same file format and conventions. A shared misreading of a convention (for example, the field-element reading for the GF(81) file's `poly`) would not be caught by this pair. For the GF(81) file, `build_haar2.py` and `check_haar_indep.py` each implement their own GF(81) arithmetic, which gives some independence there, but it is not a fully separate reading of the header.
* `check_haar_indep.py` prints `RESULT VALID ...` rather than the `VALID d=... D=...` line that the reference checkers print; both are recorded verbatim in the reports.
