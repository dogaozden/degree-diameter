# c6 notes: bi-coset graphs of Z_m x|_r Z_k with stabiliser H = <(0, k/h)>

## Model (what bicm computes)
- G = Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l), r^k = 1 mod m, k = h*kp.
- H = <(0,kp)> of order h; zeta = r^kp mod m (action of H on Z_m); need zeta != 1.
- Vertices: right cosets (a, j mod kp) on side A and side B, n = 2*m*kp.
- Edges: (a,j)_A ~ (a + r^j u, j + v)_B for (u,v) in N0, |N0| = 4, N0 invariant under (u,v) -> (zeta u, v).
  Well-definedness is asserted in mkedges.py (independent group-coset construction).
- Both sides are vertex-transitive, so the two roots (A: 0, B: nv) decide the diameter.
  Score = far vertices from root A + far vertices from root B (D = 9).
- Normal form: scaling u -> c u (unit c) and shifting v -> v + t are isomorphisms. Let s* be the largest zeta-orbit
  size in N0. Some pair of size s* can be moved to (d, 0), d | m, so enumerating the first object over divisors d and
  all completions with objects of size <= s* covers every N0. N0 with all pairs zeta-fixed (s* = 1) are disconnected
  (a stays in a coset of Fix(zeta) != Z_m) and are skipped.

## Files (all in this folder)
- bicm.c: enumerator + two-root BFS. Build: `gcc -O3 -march=native -o bicm bicm.c` (`-DDIAM=d` for other diameters).
  Usage: `./bicm FAMFILE START exh|smp S BUDGET` (family lines "m kp h r gG"; smp = S uniformly sampled normal forms).
- famlist.txt: 9,530 families with kp >= 2, |G/G'| = k*gcd(r-1,m) <= 309, n = 2*m*kp in [4972, 5600]
  (r taken up to r -> r^t, gcd(t,k)=1). famk1.txt: 3,322 kp = 1 families (H = whole complement).
- famtop.txt, famtop2.txt, famtop3.txt, famtop4.txt: families searched exhaustively (81 + 171 + 318 + 5,477).
- screen400.txt: 400-sample screen of famlist.txt (analyse.py -> screen_ok.json). scr_k1.txt: 300-sample screen of famk1.txt.
- exh_top.txt .. exh_top4.txt: exhaustive outputs. exh_all.json: merged exhaustive table.
- mkedges.py m kp h r OUT u1 v1 u2 v2 u3 v3 u4 v4: independent edge list from group cosets (asserts well-definedness).
- chk/brute.py m kp h r [D]: independent brute force over all zeta-invariant 4-sets (no normal form). Used only for checks.
- best101.edges, best219.edges: the two best graphs (edge lists).

## Validation
- bicm on 73 36 2 5 (prime Frobenius, the director's case): best 88 (two roots), matches the director's bicos result.
- bicm on 101 25 2 4: best 16, matches tools/bicos 101 50 2 4 (16).
- Composite cross-checks against chk/brute.py (all zeta-invariant sets, no normal form), same minimum:
  21 2 3 4 (96 at D=3, 56 at D=4); 21 3 2 5 (154 at D=3, 56 at D=4).
- Best graph checks: best101.edges (mkedges, n = 5050): tools/apsp gives diameter 10 (RESULT INVALID); score48 gives
  far pairs 20200 = 2525 * 16 / 2, consistent with 16 far vertices (two roots). best219.edges (n = 5256): diameter 10,
  far pairs 36792 = 2628 * 28 / 2.

## Results
- Exhaustive over 6,047 family entries (4,877 distinct (m,kp,r) graphs; h=4 entries with the same m,kp,r are the same
  graph as the h=2 entry). Global minimum: 16 far vertices (two roots), at m=101, kp=25 (k=50), h=2, r=4, zeta=-1,
  n = 5050, N0 = {(1,0),(100,0),(0,10),(0,12)}, 2 normal forms tie.
  Next: 28 at m=219, kp=12 (k=24), h=2, r=17, n = 5256; 38 at m=127, kp=21, r=5, n = 5334;
  46 at m=95, kp=27, r=14, n = 5130; 48 at m=505, kp=5, r=6, n = 5050; 56 at m=455, kp=6, r=37, n = 5460.
  Prime Frobenius cases: 73 36 2 5 gives 88 (n = 5256, as the director reported); 181 15 2 36 gives 62 (n = 5430).
- By h (exhaustive): h=2 min 16, h=4 min 16 (twins), h=3 min 394.
- Tier 4 (ncand <= 10,000, 5,477 families): best 218 (m=442, kp=6, r=115, n = 5304).
- No family reached 0 or any value below 16. Nothing close to the record n = 4,970+ with diameter 9.

## Coverage and limits (honest)
- Exhaustive: 6,047 family entries: every kp >= 2 family with <= 10,000 normal forms, plus every family with sampled best <= 1000 and <= 100,000 normal forms.
- Sampled only (400 normal forms, not exhaustive): 3,483 kp >= 2 families, of which 1,244 have > 100,000 normal forms
  (sampled min 1,006 among the sampled-only families). Sampling is not reliable above ~1000: for m=550, kp=5, h=4,
  r=39 the sample gives 968 and the exact minimum is 298; for m=304, kp=9, h=4, r=15 it gives 604 and exact 106.
  So a sampled-only family could still hide a low minimum; these were not all searched.
- kp = 1 (3,322 families, H = complement, bi-Cayley over Z_m): sample min 8,486 (two roots). Not exhaustive.
- Only the card's H = <(0,kp)> (a = 0) family was searched; other order-h subgroups (a,kp) for composite m were not.

## How to rerun
- Build: `gcc -O3 -march=native -o bicm bicm.c`
- One family: `printf "101 25 2 4 1\n" > f.txt && ./bicm f.txt 0 exh 0 80`
- Batch with time budget (prints NEXT idx to resume): `./bicm famtop4.txt 0 exh 0 82 > out.txt`
- Graph check: `python3 mkedges.py 101 25 2 4 g.edges 1 0 100 0 0 10 0 12 && ../../tools/apsp g.edges 4 9`
