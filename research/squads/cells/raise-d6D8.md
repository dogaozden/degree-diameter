# Cell (Δ, D) = (6, 8), bipartite: raise attempt (job "raise-6-8", 2026-10-25)

## Status
- Record held: **31,680 vertices** (2·|G|, G = PSL(2,11) × Z_24, |G| = 15,840), Haar graph with S chosen as three free
  orbits of size 2 under an order-2 automorphism (`ORBIT="2 3 0"`). File: `research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`.
  It was found by the table-squad session (branch `claude/degree-diameter-table-squad-0xgp3g`, 24 s, 334k evaluations) and is
  independently checked there (build_haar2.py, apsp.c). Table value 29,790; Moore bound 195,312.
- This session: **no improvement**. See the evidence below. Every candidate group with |G| ≥ 15,841 that I tried plateaued
  at cost 8 or above; no run found a valid S.

## What was run (all `haar_sym`, ORBIT="2 3 0", k = 2, m = 3, f = 0, THREADS = 1)
| wave | groups (|G|) | time per run | best cost (uncovered elements) |
|---|---|---|---|
| 1 | sl 7×Z48 (16128), pgl 8×Z32 (16128), psl 13×Z15 (16380), psl 11×Z25 (16500) | 900 s | 8, 8, 10, 14 |
| 2 | psl 19×Z5 (17100) seeds 1, 2; sl 13×Z8 (17472); psl 13×Z16 (17472) | 1200 s | 10 / 8, 9, 13 |
| 3 | psl 17×Z7 (17136), psl 23×Z3 (18216), sl 11×Z13 (17160), psl 11×Z26 (17160), prod sl3×sl9 (17280), psl 9×Z48 (17280), prod psl3×sl7×Z4 (16128), prod psl3×psl7×Z9 (18144), sl 9×Z24 (17280), prod psl3×sl4×Z23 (16560) | 600 s | 9 (best), others 14–26 |
| 4 | psl 19×Z5, sl 13×Z8, prod sl3×sl9×Z1, prod psl3×sl7×Z4 with ORBW = 3 | 5400 s | see the bottom of this file |

Protocol that is known to work here: `ORBIT="2 3 0" THREADS=1 ./haar_sym 6 8 <secs> <seed> 8 out.txt psl 11 24` (the
record was 24 s). Plateaus form within 1–2 minutes at N ≥ 16k and then stay put (the same pattern as the table squad's rounds 2–6).

## Evidence that the winner is special (and why the next rung is hard)
- Random-sample screen (`tools/orb_screen.py`, RANDORB, k = 2, auto α): PSL(2,11) × Z24 at N = 15,840 has minimum cost 5 and
  1 % quantile 30 over 20,000 samples. The best candidates at N ≥ 16,128 have minimum 12–30 and 1 % quantile 46–70 (5,000–20,000
  samples). Files: `research/squads/raise-d6D8/screen_2_3_0_15841_16700.txt` and `screen_2_3_0_15841_22000.txt`.
- α sweep (`research/squads/raise-d6D8/alpha_sweep.sh`, every conjugating element `ALPHA=i`, RANDORB = 5000):
  on the record group the best α has minimum 4 (the used α has 5; 56 valid α, minimum 4–11). On the candidates the best α has
  minimum 10 (psl 13×Z15), 14 (pgl 8×Z32), 17 (sl 7×Z48), 20 (psl 11×Z25). No α closes the gap. Logs in `alpha_sweep/`.
- The screen's candidate window above 15,840 is almost empty of usable groups: 15,900–15,990 has only A5-type or
  A4×PSL(2,3)-type groups, which have random minima of 1,900–2,600 (degenerate, many word collisions).
- Effort law (research/structured STRUCTURE.md §9.1: evals ≈ 1e5·exp((μ_A − 13)/2)): for the record, μ_A ≈ 16.6 and the law
  predicts ~6e5 evaluations (measured 3.3e5). For the N = 16k candidates it predicts 1e6–1e7, but the 15-minute runs (8e7 to
  1e8 evaluations each) failed. So the law does not describe this regime; I would not trust its predictions above 15,840.

## Negative results (from the other sessions, consistent with this one)
- Table-squad round 2–6: k = 2 on other cells was worse than k = 3; at (6,8) the k = 2 rungs 16,128–16,500 stop at 5–14
  (A4×PSL(2,7)×Z8: 89 valid involution α, all best end at exactly 5).
- structured-search §8: k = 3 with two free orbits (f = 0) on PSL(2,9)×Z43 stops at cost 3 after 6·10⁷ evaluations, and the
  orbit space (N/3)²/2 is too small for μ/3 ≈ 9.4 to leave a solution; one orbit (m = 1) is hopeless at Δ = 6.
- Random S (no symmetry) reached 30,576 (SL(2,13)×Z7) only; the orbit method is the only route that beat it.

## Verdict (so far)
Within this session's budget, the orbit method with k = 2 has no valid S above 15,840 on any group I could screen
(PSL/SL/PGL(2,q) × Z_n and the small products in the 15,841–22,000 window). The plateaus at cost 8–10 look like a floor for
these groups, not a lack of time. The remaining routes I did not try (non-cyclic abelian factors, metacyclic/Heisenberg
groups with k = 2, a Frobenius-type α of order 2 at this size) are not supported by the existing tools without new code.
