# Cell (Δ, D) = (10, 9): raise-d10D9, round 3 (Haiku worker)

Branch: claude/raise-d10d9-round3-d4tu88. Builds on round 2 (claude/raise-d10d9-round2-153lq9, merged here) and
round 1 (research/squads/cells/raise-d10D9.md). Read those first; their dead ends are not repeated here.

## Bar

Record held on the round-2 branch: **8,418,120** = 2·|PSL(2,59) × Z41| (psl 59 x Z41, k=5 m=2 f=0, ORBW=5 RESTART=1,
research/frontier/sols/d10D9_psl_59_41_orb5f0_ORBW5RESTART1_s12.txt). The brief's 8,003,856 is out of date.
Window for a new record: N > 4,209,060 (2N > 8,418,120).

## Window screen (orb_screen --list, N in (4,209,060, 4,500,000])

μ rises steeply with N: 42.5 at N = 4.21M, 44.8 at 4.23M, 48 at 4.25M, 54 at 4.29M. Round 2's random-S screen
(RANDORB 1500) and the annealing results at μ 42–45 are the reference. Candidates that have order-5 elements and
an α that moves every quotient (k = 5), with random-S cost tails (300 samples, this round):

- psl 25 x Z541 (N 4,219,800, μ 43.8, fix 24): min 38, p1 111, p10 176, median 356. Tail worse than the solved groups.
- pgl 25 x Z271 (N 4,227,600, μ 44.8, fix 24): min 64, p1 86, p10 190. Round 2 annealing best 32 after 1 h.
- sl 25 x Z271 (μ 44.8, fix 49): min 66 (round 2 screen). Weak.
- psl 19 x Z1231 (N 4,210,020, μ 42.5, fix 9): min 110, p1 191. Large cyclic factor, poor mixing.
- prod psl 5 psl 5 x Z1171 (A5 x A5, N 4,215,600): random cost 7.7·10⁶, |Fix| reported 299: the product path
  looks broken for this group. Dropped (not a real lead until the evaluator is checked).

k = 3 (Δ = 1 + 3·3, f = 1) candidates with μ 42–45, random cost tails (300 samples):

- **prod psl 7 x sl 11 x Z19** (N 4,213,440, μ 42.96, |Fix| 35): min 42, p1 60, p10 88, median 158. The best
  random tail in the window, close to psl 59 x Z41 (min 23, p1 51). **Lead.**
- **prod sl 7 x psl 11 x Z19** (same N, μ 42.96, |Fix| 35): min 54, p1 60, p10 98, median 156. **Lead.**
- prod sl 3 x sl 16 x Z43 (N 4,210,560, μ 42.6, |Fix| 89): min 94, p1 102. Weak.
- psl 31 x Z283 (N 4,211,040, μ 42.7, |Fix| 14): min 117, p1 132. Weak (round 1 best 30).
- prod sl 3 x sl 11 x Z133 (μ 43.0): min 174. prod sl 3 x sl 8 x Z349 (μ 44.0): min 304.
  prod psl 3 x psl 19 x Z103 (μ 44.7): min 114. All weak.

## Runs (round 3, started 2026-10-26 01:20 UTC)

Four single-thread queues on the two leads, k = 3 m = 3 f = 1 ORBW=5 RESTART=1, 1 h per seed (tools/orbq.sh).
Logs and solutions: research/structured/runs/d10D9_round3/out_{P1,P2,Q1,Q2}/ (P = psl 7 x sl 11 x Z19, Q = sl 7 x psl 11
x Z19). Eval rate about 95 per second on prod groups (round 2's psl groups: about 122 per second).

Status: see the log at the bottom of this file.

## Log

### 2026-10-26 01:20 UTC: start
- Four queues launched: P1 seeds 1, 3, 5; P2 seeds 2, 4, 6 (prod psl 7 sl 11 Z19); Q1 seeds 1, 3, 5; Q2 seeds 2, 4, 6
  (prod sl 7 psl 11 Z19). Each seed 3600 s.
### 2026-10-26 02:12 UTC: 52 min in, no solve

- All four runs (P1, P2, Q1, Q2) sit at best cost 18 after 3,094 s and about 3·10⁵ evaluations each (95 per s).
  Cost 18 with ORBW=5 is about four uncovered orbits or fixed points, and it has not moved for 30 minutes.
- For comparison, round 2's solved group (psl 59 x Z41) was at cost 2 to 10 within an hour, and its solve came at
  226k evaluations. These two prod leads look weaker than the solved groups. Seeds 1 and 2 finish at about 02:20;
  queues then continue with seeds 3 to 6. The verdict waits for those seeds.
