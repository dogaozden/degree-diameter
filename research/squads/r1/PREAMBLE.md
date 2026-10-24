# Squad round 1 preamble (read this first; it applies to every card)

Goal of the round: bipartite (Δ, D) records at **diameter D = 5**, using Haar graphs with an automorphism-symmetric
connection set (the "orbit search" of `haar_sym`). Opus calibrated it today: at (9,5) on SL(2,11) (N = 1320) the orbit
search solved in 0.1 s, where plain annealing stalls at 2 uncovered after 12M evaluations.

## Objects

- Haar graph H(G,S): vertices G × {A,B}, edges (g,A) ~ (sg,B) for s in S, |S| = Δ. Order 2|G| = 2N.
- Diameter ≤ 5 iff (S⁻¹S)² = G and (SS⁻¹)² = G. Word count W = 1 + Δ(Δ−1) + Δ(Δ−1)³.
  Difficulty μ = N·exp(−W/N) (smaller is easier). Random annealing walls at μ ≈ 35–40 at D = 5.
- `ORBIT="k m f"`: S = {e} ∪ (f−1 generators fixed by α) ∪ (m orbits of size k) of an automorphism α of order k,
  with Δ = f + k·m. **f = 0** means S is m free orbits only (no identity; allowed). α = conjugation by an element of the
  base group Q, times z ↦ r·z on the cyclic factor Z_n.
- What matters (Opus's calibration, keep it in mind):
  1. **α-fixed points are expensive at D = 5.** haar_sym prints `|Fix(alpha)|` and `fixed-point misses ~ X`. Each fixed
     element costs about e^(−λ/k) expected misses (λ = W/N ≈ 3.5), against e^(−λ) for a free one. Keep |Fix| ≤ ~12.
     A cyclic factor Z_n gives few fixed points only when every prime of n is ≡ 1 mod k (then z ↦ rz fixes only 0);
     otherwise α fixes all of Z_n and |Fix| explodes (e.g. SL(2,7) × Z_4 with k = 3: Fix 23, failed).
  2. **Nearly-abelian groups fail.** `meta` groups with their scaling α (best 924 uncovered at (10,5)) and `heis` (78 at
     (6,5)) are bad. SL(2,q), PSL(2,q), PGL(2,q) (note sl 4 = psl 5 = pgl 4 = A5), their products, times a small Z_n, work.
  3. A good run is: estimated μ/k + fixed-point misses ≤ ~25. Calibration points: (9,5) SL(2,11) μ/k 12.7 + 7.4 solved
     at once; (11,5) A5 × Z49 (psl 5 49) k=3 m=3 f=2, μ = 67, best 6 uncovered after 120 s; (10,5) SL(2,13) k=3 m=3 f=1,
     μ = 74, best 8 after 120 s; PSL(2,7) × Z13 same cell best 14.

## Tools (already built; do not rebuild)

```
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
T=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/tools
README: /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/README.md
```

- Search (one run; `d D seconds seed K outfile GROUP... n`):
  `ORBIT="3 3 2" timeout 900 nice -n 10 $B/haar_sym 11 5 600 1 8 OUT.txt psl 5 49 > OUT.log 2>&1`
  The last token is the cyclic factor n (use 1 for none). Groups: `sl q`, `psl q`, `pgl q` (q a prime power),
  `agl1 q`, `prod G1 G2` (e.g. `prod psl 5 psl 7 1` = A5 × PSL(2,7)), `meta m k r`, `heis q`.
  The log ends with `RESULT ... best=<uncovered>`; best=0 means solved, then it prints `full diameter check: OK` and
  `wrote OUT.txt`.
- Useful env vars: `ORBW=k` (weigh uncovered fixed points as a whole orbit), `RESTART=1` (reheat from fresh random
  orbits), `RANDORB=m` (only sample m random symmetric S, print the cost quantiles; fast screen), `ALPHA=<index>`
  (choose the conjugating element), `AR=<r>` (choose r on Z_n). Seeds: change the 4th argument.
- Screen many groups in an order window (ranks Q × Z_n by the lower tail of random symmetric costs):
  `python3 $T/orb_screen.py d 5 LO HI "k m f" --bin $B/haar_sym --samples 300 [--anyn] [--fams sl,psl,pgl,prod]`
  Without `--anyn` it only lists n whose primes are ≡ 1 mod k (few fixed points). `--list` just lists candidates with μ.
- Independent check of a solution (must say VALID):
  `python3 /home/user/degree-diameter/research/frontier/build_haar2.py OUT.txt OUT.edges.txt`
  (handles sl/psl/pgl/agl1/prod/meta/cyc, not heis). Then `rm OUT.edges.txt` unless it is a record.

## Machine rules (shared box: 4 cores, 15 GB, 8 squad members)

- **One heavy process at a time** per card, single-threaded (`THREADS=1` is the default), always under
  `timeout 900 nice -n 10`. Runs of 300–600 s are the right size. Stay under ~1.5 GB memory (D = 5 runs use a few MB).
- Write files **only** under `/home/user/degree-diameter/research/squads/r1/<your card>/`. No git commands, no edits to
  any other file. Do not leave processes running when you return: wait for every run to finish (or kill it).
- Total budget: about 45 minutes of wall clock. Spend it on runs, not on reading code.

## What to return (short, plain text)

1. The idea tried (groups, ORBIT parameters, env vars).
2. Exact commands of the best runs.
3. Results: per group, N, 2N, μ, |Fix|, best uncovered reached (and seconds). Any best=0: the solution file path and the
   build_haar2.py VALID/INVALID line. Say clearly whether it beats the target.
4. Files written.
5. The one thing you would try next.
