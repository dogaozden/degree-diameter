# c21 notes (card: 1,6|1,6 on orders 300, 306, 312; c18's type, 686 = 294 is c18's)

## Model
Type "1,6|1,6", N = 5,1,1,0 (only connected solution for k = 6; see c18/NOTES.md). A0 = G, B0 = G, A1 = G/H, B1 = G/K
with |H| = |K| = 6, H and K any subgroups of order 6 (cyclic C6 or S3). n = 7|G|/3: 300 -> 700, 306 -> 714, 312 -> 728.
Cost = number of (orbit representative, vertex) pairs at distance > 5, 4 representatives. bad (far unordered pairs)
is about cost * |G|.

## Tools (copied from c18, changed)
- t18.c -> t18 (compiled). Usage: `t18 GROUP_TABLE 6 5,1,1,0 SEED ITERS TENURE OUT [HGEN KGEN]`.
  Changes vs c18: argument check fixed (was requiring 9 args); subgroups of order 6 include S3 (env CYCLIC=1 restores
  cyclic only); env SAMPLE (random candidate values per slot per step), SUBS (random subgroups per move), TLIM (seconds);
  candidate cutoff (cost_now stops once the partial total exceeds the best candidate so far).
- screen21.sh TLIM SEED DEADLINE TABLES... -> scan/screen.tsv (group, nsub, best, sec). Keep foreground calls < 120 s
  (or pass timeout 300000 to the Bash tool; a longer call is backgrounded).
- groups/: order 294 (11), 300, 306, 312 tables copied from c18/groups.

## Calibration
- 294_11 (c18's 686 case), SAMPLE=60 SUBS=20: 20 s -> cost 5; 60 s (cyclic subgroups only, full moves) -> cost 2 (= c18).
- Machine: load ~9 on 4 cores, nice 10: about 0.2 s wall per step with SAMPLE=60.

## Results
(see scoreboard.tsv for personal bests)

## Screen 1 (t18, SAMPLE=60 SUBS=20, 20 s wall, seed 1, groups 300_1..300_18)
- 300_13 cost 24, 300_14 cost 45, 300_15 cost 33, 300_16 cost 122 (nsub 1..25). 20 s is too short to rank: 294_11 gave 5-9 at 20 s and 2 at 60 s.
- Plan: finish order 300, then 306 and 312, then 5-min deep runs on the best 3-5 with several seeds.
