# Regular diameter-6 graphs (Problem 4, literal ask) — p4-regular-opus, report 1 (08:08)

Saved by the main session from the agent's message (the harness blocks subagents from writing report files).

## Why the sides differ
A0 is balanced: (q+1)(q³+1) points and as many lines (exact whiskers force this). The excess comes from higher levels:
A1 holds q³+1 lines (v and S) but only q+1 points (those on v), and A2 = {v}. Line excess = (m−1)·m·(q³−q+m):
244, 1444, 2644, 4372 for m = 2 at q = 5, 9, 11, 13, and 13122 for m = 3 at q = 13 — matching the measured sides. Every
deficient vertex is a line (whisker versions, S-line versions, v versions). Balancing by levels inside this family is
impossible: with v at level 2, no line at distance 4 from v can be in A0; every point not on v has such a line, so the
only level-1 points are the q+1 points of v.

## Theorem R
For q an odd prime power and m ≥ 2, there is a (q+m)-regular bipartite graph of diameter 6 on
n = 2(q+1)[q⁴+q²+1 + (m−1)(q³+m+1)] vertices: 2(q+1)(q⁴+q³+q²+4) at Δ = q+2, 2(q+1)(q⁴+2q³+q²+9) at Δ = q+3.
Proof.
1. Twins. For an S-line ℓ ≠ v, the m versions ℓ^{a·} all have neighbourhood {p^a : p on ℓ}; likewise v^{ab·} have
   {x^{ab} : x on v}. So there are mq³+m² twin classes of size m, all on the line side.
2. Twin lemma. Deleting a vertex that still has a twin changes no distance among the remaining vertices (swap it for its
   twin on any shortest path). Deleting lines never changes another line's neighbourhood, so up to m−1 deletions per
   class are allowed. Delete exactly the excess; (m−1)(mq³+m²) are deletable.
3. Degrees. Each point loses at most m−1 neighbours, all from one class, so every degree stays in [q+1, q+m]. Both
   sides end with equal total deficit T.
4. Completion lemma. Bipartite, equal sides, deficits ≤ s, and T > 2s(Δ+s+1): Hall on stubs gives a perfect matching of
   compatible stubs (min degree ≥ T/2); swaps remove any repeated pair. Added edges cross sides and cannot increase
   distances. ∎
Alternative step 1 (m = 2): keep only q⁴−2q³−q²+2q−4 whiskers; the sides then balance directly (hats Theorem 3), same n.

## Graphs (research/p4/regular/graphs; all exactly regular, equal sides)
| (Δ,6) | q | n | table | unbalanced (hats) | check |
|---|---|---|---|---|---|
| (7,6) | 5 | 9348 | 8992 | 9592 | verify_record VALID (agent and main session), 7-regular, sides 4674/4674 |
| (11,6) | 9 | 147500 | 142464 | 148944 | bigcheck VALID (agent); main session re-check running |
| (13,6) | 11 | 386328 | 374452 | 388972 | bigcheck VALID (agent); main session re-check running |
| (15,6) | 13 | 866068 | 842048 | 870440 | bigcheck VALID (agent, 700 s); main session re-check running |
| (16,6) | 13, m=3 | 927724 | 884062 | 940846 | sides 463862/463862; checks running |
Tool: regularize.py IN Δ OUT. Twin classes found: mq³+m² (254, 1462, 2666, 4398; 6600 of size 3).

## Improving on the trim
A balanced exact structure with half the level-1 centres at points would give about 9576 at q=5. Regulus switching
fails (regulus.py: off-Π points split into 525 groups of 6 at q=5; shadows are the opposite regulus of a unital block,
centres pairwise opposite; leaves on a point centre's lines are impossible, so the point side loses q−1 per switched
line). The q=3 ILP gives 984 with sides 476/508, so 952 balanced against 968 from trimming. Mixed-centre structures
without the spread are open.

---
# Report 2 (FINAL, 08:42)

All 5 regular diameter-6 graphs pass bigcheck; the (7,6) graph also passes verify_record. Rebuild: `python3
regularize.py IN Δ OUT [seed]` (deterministic per seed).

| (Δ,6) | n | file | degrees | checks | table | hats |
|---|---|---|---|---|---|---|
| (7,6) | 9348 | reg_q5_d7_n9348.json | 7:9348, sides 4674/4674 | verify_record, bigcheck, check_big | 8992 | 9592 |
| (11,6) | 147500 | reg_q9_d11.txt | 11:147500 | bigcheck, check_big | 142464 | 148944 |
| (13,6) | 386328 | reg_q11_d13.txt | 13:386328 | bigcheck; check_big running | 374452 | 388972 |
| (15,6) | 866068 | reg_q13_d15.txt | 15:866068 | bigcheck (700 s) | 842048 | 870440 |
| (16,6) | 927724 | reg_q13a3_d16.txt | 16:927724, sides 463862/463862 | bigcheck (2057 s) | 884062 | 940846 |

Main-session independent bigcheck (research-lab/verify/bigcheck, written without the agents' code), all VALID,
exactly regular, equal sides, exact diameter 6: (7,6) also verify_record; (11,6), (13,6), (15,6) 433034/433034, (16,6) 463862/463862.

Simpler alternative proof, same n: keep only q⁴−2q³−q²+2q−4 exact whiskers (q⁴−3q³−q²+3q−9 when m = 3); sides balance
directly through hats Theorem 3, then the completion lemma. Delorme's own graphs (no whiskers) have the opposite excess
(point side larger), so the table graphs are not regular either.

## Left / negative results
1. In this family n = 2|P| is the ceiling (with v at level 2 the only level-1 points are the q+1 points of v; A0 is
   already exact).
2. A balanced structure with point centres would allow at most about 2N + 2(N−c)/q + 2c: 9576 at q=5, ~148920 at q=9.
3. Regulus switching fails (regulus.py: off-Π points form q²(q²−q+1) groups of q+1, opposite reguli of unital blocks;
   trading a block for point centres loses q−1 points per line). q=3 ILP: 952 balanced vs 968 by trimming.
4. Random mixed codes + leaf ILP (mixcode.py, q=3): A0 ≈ 80 vs exact 114.
5. Open: an exact structure with (q³+1)/2 point centres and (q³+1)/2 line centres without the Hermitian spread
   (natural for self-dual q = 9).

Novelty: regular graphs are the literal ask of AL Problem 4; as far as we know these are the first regular bipartite
graphs of diameter 6 above the table at Δ = 7, 11, 13, 15, 16. The twin and completion steps are routine; the real
input is hats Theorem 4.
