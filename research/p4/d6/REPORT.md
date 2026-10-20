# Problem 4, diameter 6 (d6-opus) — REPORT

Status: in progress (last update 2026-10-19 ~23:45). Numbers below are current; see the end for what is running.

## 1. Table values (diameter 6)

Source: Combinatorics Wiki, "The Degree Diameter Problem for Bipartite Graphs", table "as of January 2012"
(downloaded 2026-10-19). Open cells are those with Delta-1 not a prime power.

| Delta | q used | table value | Moore bound M_b(Delta,6) | table construction |
|---|---|---|---|---|
| 7  | 5  | 8 992   | 18 662    | Delorme–Farhi duplication |
| 11 | 9  | 142 464 | 222 222   | Delorme–Farhi duplication |
| 13 | 11 | 374 452 | 542 906   | Delorme–Farhi duplication |
| 15 | 13 | 842 048 | 1 158 390 | Delorme–Farhi duplication |
| 16 | 13 | 884 062 | 1 627 232 | Delorme–Farhi duplication |

**Where the table values come from.** Delorme [D85, Sec. 8(b)]: H(q) has q^3+1 pairwise opposite elements
(Thas [T80]; the Hermitian spread). Take A2 = one of them, A1 = A2's neighbours plus the q^3+1 elements, A0 = A1 plus
its neighbours, and "dédoubler" A0, then A1, then A2. His worked example is exactly 7812+912+2(132)+4 = 8992.
In general (checked against all four Delta = q+2 cells):

  table(q+2, 6) = 2(q+1)(q^4+q^2+1) + q^4 + 4q^3 + q^2 + 4q + 10      (q = 5, 9, 11, 13 give 8992, 142464, 374452, 842048).

Delta = 16 is the same with tripling instead of doubling on H(13): 804468 + 2(|A0|-|A1|) + 8(|A1|-1) + 26 = 884062.

## 2. The construction: Delorme's levels plus whiskers

**Level lifts** (a reformulation of [D85, Sec. 7]). G bipartite, levels lev: V -> {-1,0,1,2,...} with
|lev(x)-lev(y)| <= 1 on edges. A vertex of level k gets b^(k+1) versions (strings of length k+1 over b letters);
a level -1 vertex keeps one version (the empty string). (x,a) ~ (y,c) iff x ~ y and one of a, c is a prefix of the other.

- *Degree.* deg(x,a) = deg(x) + (b-1)·#{neighbours of higher level}.
- *Walk lifting.* If W is a walk x = x_0, ..., x_m = y in G with minimum level mu, and a, c agree on their first mu+1
  letters, then (x,a) and (y,c) are joined by a walk of length m (take the prefixes of a padded with zeros up to the
  minimum point, the prefixes of c after it).
- *Diameter lemma.* Let A0 = {lev >= 0}, L = {lev = -1}. If diam G <= D and every two x, y in the same component of
  G[A0] (x = y allowed) have some z in L with d(x,z) + d(z,y) <= D, then the lift has diameter <= D.
  (Pairs with an end in L, or ends in different components of G[A0], use a shortest path, which meets L.)
- Bipartite: the lift of a bipartite graph is bipartite.

**Theorem D.** Let H be a generalized hexagon of order (q,q), S a set of q^3+1 pairwise opposite lines, v in S,
V the lines other than v meeting v, and W a set of lines (not in S or V) meeting lines of S - v, such that every
point off the lines of S lies on at most one line of V ∪ W. Set lev(v)=2, points of v: 1, V: 0, S-v: 1, points
of S-v: 0, W: 0, others -1, and b = 2. The lift is a bipartite graph of maximum degree q+2, diameter 6, and order

  2(q+1)(q^4+q^2+1) + q^4 + 4q^3 + q^2 + 4q + 10 + |W|.

With b = 3 it has maximum degree q+3 and order 2(q+1)(q^4+q^2+1) + (Delorme's tripling gain) + 2|W|.

*Proof sketch* (full case list in Section 4). Counting gives N = (q^3+1)(q^2+q+1): every line not in S meets exactly
one line of S. Hence each L-line has exactly one A0 neighbour (its S-point), each S-point has one higher neighbour
(its S-line), each point of v has v, each V-line its v-point, and each point off S at most one A0 line (the
hypothesis on W; two V-lines never meet off v by girth 12). So degrees are <= q+2. The components of G[A0] are the
radius-2 tree around v and the stars s + points of s + whiskers at those points; in each, every pair has an
L-vertex z with d(x,z)+d(z,y) <= 6 (Section 4). The diameter lemma finishes it.

Whiskers are line copies whose stand-in at the spread point is the point's Delorme copy (Theorem B language).

**Bounds on |W|.** Each whisker uses q of the q^5 - q^3 free points (off S, not on V-lines), so |W| <= q^4 - q^2.
Any maximal whisker set has >= (q^5-q^3)/(q^2+1) > q^3 - 2q elements (q^5 - q^3 candidates, conflict degree <= q^2),
so **n_b(q+2,6) >= table value + q^3 - 2q + 1 for every prime power q**, i.e. Delorme's family is never optimal.

## 3. Results

| Delta | table | ours | gain over table | file | verified |
|---|---|---|---|---|---|
| 7 | 8992 | **9592** | +600 | graphs/h5_whisk600_n9592.json (W: graphs/h5_whisk600_W.txt) | diam.c and diamp.c OK; verify_record.py running |
| 7 | 8992 | 9480 | +488 | graphs/h5_whisk488_n9480.json (earlier, ILS) | diam.c OK |

At q = 5 the annealer finds |W| = 600 = q^4 - q^2, the maximum (every free point used), in under a minute, twice
(seeds 1, 2). Both perfect packings have the same shape: 100 = q^3 - q^2 spread lines carry a whisker at each of
their q+1 points, and the other q^2 spread lines carry none. If that holds for all q, Theorem D gives
n_b(q+2,6) >= 2(q+1)(q^4+q^2+1) + 2q^4 + 4q^3 + 4q + 10.

Reproduction: graphs/h5_delorme_n8992.json is Delorme's graph rebuilt (diam.c: max degree 7, diameter 6).

## 4. Diameter case list (component C_s = s, its points p_i, whiskers w at p_i; C_v = v, points u, V-lines m)

Parity: for x, y on opposite sides the bound needed is 5. r denotes a free point on a whisker or V-line.
- (s,s): z at distance <= 3. (s,p): z = an L-line at p (1+2) or r on a whisker at p (2+3). (s,w): r on w (1+3).
- (p,p'): L-line at p' (1+3) or r on a whisker at p' (2+4). (p,w'): r on w' (1+4). (w,w'): r on w (1+5).
- (v,v): r (3+3). (v,u): r on a V-line at u (2+3). (v,m): r on m (1+3). (u,u'): r on m' at u' (2+4).
  (u,m'): r on m' (1+4). (m,m'): r on m (1+5).

## 5. Files
- hexq.py, delorme_q5.py, lift.py, whiskers_q5.py, whisk_ils.py, whisk_greedy.py: Python version for q = 5.
- hexgen.c: H(q) for q = p, p^2 (builds lines from Tits' equations, checks counts). hex/hex_q{q}.bin.
- d6lift.c: Hermitian spread, Delorme levels, whisker annealing, lift output. diam.c: bit-parallel diameter check.

## References
- [D85] C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. 6 (1985) 291–302, Sec. 7–8.
- [T80] J. A. Thas, Polar spaces, generalized hexagons and perfect codes, J. Combin. Theory Ser. A 29 (1980) 87–93.
