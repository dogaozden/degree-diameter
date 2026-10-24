# Squad round 2 preamble (read this first; it applies to every card)

Goal of the round: raise our Haar records at **Δ = 6..9, D = 7..10** with orbit-symmetric connection sets of a kind the
earlier orbit search never used: **k = 2** (orbits of size 2) and **k = 4** (orbits of size 4). Opus found today that
k = 2 cracks (6,8), which k = 3 could not: SL(2,25) with ORBIT="2 3 0" solved N = 15,600 in 201 s, then
PSL(2,11) × Z24 solved N = 15,840 in 24 s (our record was 15,288; the earlier k = 3 search found no symmetric solution
at all near 15,500, because with Δ = 6 and k = 3 there are only two orbits).

## Objects

- Haar graph H(G,S): vertices G × {A,B}, edges (g,A) ~ (sg,B), s in S, |S| = Δ. Order 2|G| = 2N.
- Difficulty μ = N·exp(−W/N), W = number of non-backtracking words of length ≤ D−1 (haar_sym prints μ). Plain random
  search walls at μ ≈ 20–25; the k = 3 orbit search reached μ ≈ 40–55 on the cells below.
- `ORBIT="k m f"`: S = {e} ∪ (f−1 fixed generators) ∪ (m orbits of size k) of an automorphism α of order k
  (conjugation by an element of the base group Q, times z ↦ r·z on Z_n), Δ = f + k·m. **f = 0** = only free orbits.
- Why k = 2 can win: at D ≥ 7, λ = W/N is 4–13, so an α-fixed element costs only e^(−λ/2) (0.01–0.1) expected misses;
  k = 2 keeps more independent orbits (Δ/2 instead of Δ/3), so the search space is much larger. For k = 2, r = −1
  on Z_n, which fixes only z = 0 (and n/2 if n is even), so **any n works**.
- k = 4 (Δ = 8: ORBIT="4 2 0") divides μ by 4 but has only two orbits; it needs a conjugating element of order 4 in
  the inner automorphism group (exists in SL(2,q) for most q).

## Our current records (vertices; N = half), μ at the record, μ at +3 %

| cell | record | N | μ | μ at +3 % | used before |
|---|---|---|---|---|---|
| (6,7) | 8,880 | 4,440 | 54.6 | 63.9 | k=3 m=2 f=0, SL(2,5)×Z37 |
| (8,7) | 43,344 | 21,672 | 38.5 | 47.7 | k=3 m=2 f=2, SL(2,8)×Z43 |
| (6,8) | 31,680 | 15,840 | 33.3 | 41.0 | k=2 m=3 f=0 (today) |
| (7,8) | 95,760 | 47,880 | 43.0 | 54.3 | k=3 m=2 f=1, PSL(2,19)×Z14 |
| (8,8) | 239,904 | 119,952 | 39.8 | 51.8 | k=3 m=2 f=2, PSL(2,17)×Z49 |
| (9,8) | 540,360 | 270,180 | 37.9 | 50.6 | k=3 m=3 f=0, PSL(2,19)×Z79 |
| (6,9) | 127,296 | 63,648 | 29.7 | 38.2 | k=3 m=2 f=0, SL(2,17)×Z13 |
| (7,9) | 462,840 | 231,420 | 38.2 | 50.7 | k=3 m=2 f=1, PSL(2,29)×Z19 |
| (8,9) | 1,316,016 | 658,008 | 23.9 | 33.2 | k=3 m=2 f=2, SL(2,37)×Z13 |
| (6,10) | 524,160 | 262,080 | 23.6 | 31.9 | k=3 m=2 f=0, SL(2,5)×PSL(2,7)×Z13 |
| (7,10) | 2,234,400 | 1,117,200 | 22.2 | 31.4 | k=3 m=2 f=1, PSL(2,49)×Z19 |

## Tools (already built; do not rebuild)

```
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
T=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/tools
README: /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/README.md
```

- Search: `ORBIT="2 3 0" timeout 900 nice -n 10 $B/haar_sym 6 8 600 SEED 8 OUT.txt psl 11 24 > OUT.log 2>&1`
  (`d D seconds seed K outfile GROUP... n`; last token = cyclic factor n). The log ends with `RESULT ... best=<uncovered>`;
  best=0 means solved, then `full diameter check: OK` and `wrote OUT.txt`.
- Groups: `sl q`, `psl q`, `pgl q` (q a prime power), `prod G1 G2` (e.g. `prod sl 5 psl 7 13`), `agl1 q`. Avoid `meta`
  and `heis`.
- Screen an order window: `python3 $T/orb_screen.py d D LO HI "2 3 0" --bin $B/haar_sym --samples 300 --anyn --top 20`
  (ranks groups by the lower tail of random symmetric costs; for k = 2 always pass --anyn). At large N lower --samples
  (each sample is one evaluation, ~0.01–0.5 s).
- Env: `ORBW=k`, `RESTART=1`, `RANDORB=m` (sampling only), `ALPHA=<index>`, `AR=<r>`.
- Independent check of a solution (must say VALID; needs ~0.5 KB per vertex, fine below ~5M vertices):
  `python3 /home/user/degree-diameter/research/frontier/build_haar2.py OUT.txt`

## Machine rules (shared box: 4 cores, 15 GB, 8 squad members + Opus)

- **One heavy process at a time** per card, single-threaded, always under `timeout 900 nice -n 10`. Runs of 300–600 s.
  Memory: keep each process under ~1.5 GB (all cells above are far below that).
- Files **only** under `/home/user/degree-diameter/research/squads/r2/<your card>/`. No git, no edits elsewhere. Do not
  leave processes running when you return.
- Total budget: about 45 minutes of wall clock.

## What to return (short, plain text)

1. The idea tried (groups, ORBIT parameters, env vars). 2. Exact commands of the best runs. 3. Results per group: N, 2N,
μ, |Fix|, best uncovered reached (and seconds); any best=0 above the record: the solution file path and the
build_haar2.py VALID line. 4. Files written. 5. The one thing you would try next.
