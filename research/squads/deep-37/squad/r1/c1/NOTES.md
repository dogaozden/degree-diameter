# c1 (census168) notes

Ran: src/gen_gsets.sh-equivalent G-set generation (squad/r1/c1/gen37.sh, MAXSETS cap), PROBE=300 estimates, then
squad/r1/c1/drive.py (orbdfs, MAXSOL=200, timeout 100 s, sharding SHARD=i/16 SHARDDEPTH=6 with a 300 s budget per G-set).
Groups: 21_1, 21_2, 14_1 (partial), 42_1..3 (cap 300), 168_42 (all 145 listed), 168_43 (cap 300, 295 listed),
plus a targeted G-set for 168_43 (girth-8 orbit types). Stopped at 00:35 UTC.

Result: 195 solution files, all apsp VALID. Two isomorphism classes: |Aut| 168 girth 8 (records/n168_new_girth8_aut168) and
|Aut| 504 girth 12 (C168.1). Both known. No new (3,7) graph on 168 vertices.

Files: census168.md (report), classes.tsv, group_summary.md, runs.tsv (run log), runs_before_shardfix.tsv (superseded),
est_rerun_shardfix.txt, classes via finalize.py, report.py, drive.py, gen37.sh, chain*.sh, sig.py.
