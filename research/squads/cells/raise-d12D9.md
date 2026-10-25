# Raise the (Δ,D) = (12,9) record (Haar graphs)

Job "raise-12-9", Haiku worker, branch `claude/raise-d12d9-bipartite-record-f510kc`.
Record to beat: **34,026,720** vertices = 2N, N = |SL(2,41) × Z_247| = 17,013,360, k = 3, m = 4, f = 0
(`research/frontier/sols/d12D9_sl_41_247_orb3f0_s1.txt`, μ = 16.3, solved in 3.8·10⁴ evaluations).
Table value 30,001,152 (survey, Table 4). Moore bound 471,589,538.

Every new record must have N > 17,013,360 and pass an independent checker:
- SL(2,p) × Z_n above 20M vertices: `research/frontier/haarcheck_sl.c` and `research/structured/tools/haarcheck2.c`/`hc2`
- PSL(2,p) × Z_n above 20M vertices: `research/structured/tools/haarcheck_psl.c`
- below 20M vertices: `research/frontier/build_haar2.py`

## Method
`ORBIT="3 4 0" THREADS=1 haar_sym 12 9 SECS SEED 8 OUT GROUP... n` (f = 0: 4 free α-orbits of size 3, no identity).
Screen: `tools/orb_screen.py 12 9 LO HI "3 4 0" --samples 600 --bin ...` (random symmetric S, ranks by lower cost tail).

## Log
(see below; newest last)
