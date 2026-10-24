# cloudcheck: independent verification of large Haar graph records

Machine: 4 cores, 15 GB RAM, 30 GB disk. Files are checked one at a time, smallest first.

| File | Expected vertices | build_haar2.py | check_haar_indep.py |
|---|---|---|---|
| d7D10_psl_49_19_orb3_s1 | 2,234,400 | VALID d=7 D=10 vertices=2234400 | RESULT VALID d=7 D=10 |
| d11D9_sl_61_37_orb3_s1 | 16,792,080 | VALID d=11 D=9 vertices=16792080 | RESULT VALID d=11 D=9 |
| d10D10_psl_389_1_orb3_s1 | 58,863,480 | VALID d=10 D=10 vertices=58863480 (peak RSS about 7.2 GB) | RESULT VALID d=10 D=10 |
| d14D9_sl_383_1_orb3_s1 | 112,363,008 | no verdict: killed by SIGKILL at peak RSS 13.9 GB, did not fit in 15 GB | RESULT VALID d=14 D=9 (peak RSS about 9.5 GB) |

Full stdout of both checkers for each file: `research/frontier/runs/cloudcheck/<file stem>.txt`.
