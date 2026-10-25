# c4 notes: referee s.2.4 and the (3,7) theorem

Scope: `research/theorems/SMALL_DEGREE_FAMILIES.md` s.2.2 ("Lifts and free actions", lines 164-167), s.2.4 (lines 246-270)
and the (3,7) bullet of s.2.5 (lines 276-285), checked against `smallfam/runs/completeness_resume.txt` and the five
run files. No git. Everything written in this folder.

## Verdict

- **(3,7) claim: no real gap.** Bases, lift logic, group-order ranges and coverage all check out, and the five runs
  contain zero solutions.
- **s.2.4 growth inequality: correct in substance,** but the universal group is under-specified (gap A).
- Two presentation gaps in s.2.4/s.2.5 (gaps B and C). None affects the theorem about graphs with more than 168 vertices.

## 1. Growth inequality N <= (2D+1)^((o+1)(Delta-1)) (s.2.4)

Checked, step by step:
- Translating S on the right, S -> S a^{-1}, gives an isomorphic Haar graph (map (g,A) -> (ag,A)), so S = {1, s_1, ..., s_d}
  with d = Delta-1. The normal form is not needed.
- Diameter <= D covers all N A-side vertices by walks of even length <= D. An A->A walk of length 2l ends at a word of
  length <= D in the s_i^{+-1}, so N <= #(ball of radius D in U) where U is the universal group.
- **U must be specified** (the text does not do it). U = M x| Z^d with M = (Z[x]/(x^o - 1))^d. Each e_i acts on M by
  multiplication by x^{j_i}, where s_i = (a_i, j_i). Generators u_i = (eps_i; e_i), eps_i the unit in coordinate i.
  The map phi(P;n) = (sum_i a_i P_i(r), sum_i n_i j_i mod k) is a homomorphism G-product (a,J)(b,L) = (a + r^J b, J+L),
  using that x -> r is a ring map Z[x]/(x^o-1) -> Z_m (r^o = 1 mod m) and that phi(u_i) = s_i.
- Counting holds: each letter adds one monomial with sign +-1 to one coordinate, so sum |P_{i,c}| <= D and |n|_1 <= D.
  The count is at most (2D+1)^d (2D+1)^{od} = (2D+1)^{(o+1)d}. The asymptotic corollary (polynomial in D for fixed o,
  so o must grow like D log(Delta-1) / ((Delta-1) log(2D+1)) up to a -1) follows.
- Numerical test, `hom_test.py` (Z_7 x|_2 Z_6, o = 3, Delta = 3, 2000 random words of length 7):
  - correct action (e_i by x^{j_i}): **0 mismatches** between phi(word) and the G-product; max |n|_1 = 7, max coefficient 6;
  - naive action (every letter multiplies by x): **1794 mismatches**.
- "Z_m x <y^o> is abelian of index o": correct.

**Gap A (precision, s.2.4 line 249-250, "Use the universal group ... x| Z^(Delta-1)").** The action of Z^(Delta-1) and the
homomorphism are never stated. Read naively (one x per letter), the map is not a homomorphism. Fix: add "e_i acts by
x^{j_i}, where s_i = (a_i, j_i)" and "phi(P;n) = (sum_i a_i P_i(r), sum_i n_i j_i)". The bound itself is unaffected.

## 2. The (3,7) claim (s.2.2 lifts + s.2.5)

**Quotient argument (s.2.2, lines 164-167): correct.** G acts colour-preservingly and freely on vertices. So no edge is
inverted, X/G has no loops, G acts freely on edges, and X -> X/G is a regular G-covering.

**Number of orbits.** Each colour class has N vertices and each orbit has |G| vertices. So the number of A-orbits equals the
number of B-orbits, m, and the number of orbits is b = 2m. b <= 6 gives m in {1,2,3}. Bases are therefore the dipole,
the 2+2 bases and the 3+3 bases.

**Base classification.** Connected loopless cubic bipartite multigraphs with m+m vertices correspond to nonnegative integer
m x m matrices with line sums 3 and connected support, up to row and column permutations. `check_bases_costs.py` enumerates
them:
- m=1: 1 class (triple edge, the dipole);
- m=2: 1 class, [[1,2],[2,1]] (`bases/b22.txt`);
- m=3: 55 labelled matrices, **3 classes**: [[0,1,2],[1,1,1],[2,1,0]] (`bases/b33_0.txt`), [[0,1,2],[1,2,0],[2,0,1]]
  (`bases/b33_1.txt`), and all-ones = K3,3 (`bases/b33_2.txt`).
This matches the base files. Section 2.5 asserts the list without this argument (it came from `basegen.py`).

**Ranges (exact).** n = b|G| with n > 168 and n <= 254 (254 is the bipartite Moore bound: from a vertex in A, the A side
has 1+6+24+96 = 127 vertices, so n = 2N <= 254; TABLE.md's Moore row gives 254 at D=7, and 168 is the D=7 column of the table):
- dipole, b=2: |G| in [85,127] (2*84 = 168, 2*128 = 256);
- 2+2, b=4: |G| in [43,63] (4*42 = 168, 4*64 = 256);
- 3+3, b=6: |G| in [29,42] (6*28 = 168, 6*43 = 258).
These are exactly the run ranges in s.2.5.

**Coverage (`check_counts.py` against GAP `NrSmallGroups`, `nrsg_out.txt`).** Every order matches, and each SmallGroup
id appears exactly once:
- Haar, 85-127: 512 rows = 512 groups;
- 2+2, 43-63: 131 rows = 131 groups;
- 3+3, 29-42: 101 rows = 101 groups for each of b33_0, b33_1 and b33_2.
- Statuses: Haar abfail 136, rank>2 259, pass 117; 2+2 rank>3 9, lift 122; 3+3 rank>4 1 (C2^5 at order 32, which needs 5
  generators, so it cannot be a connected lift over a base with 4 independent cycles), lift 100. No gap-timeout,
  too-big or skipped rows.
- **Solutions: nsol = 0 in every row of all five files.**
- Best costs match the write-up: Haar order 96 at 100 = 96+4 (ids 65 and 66, "4 vertices short"); 2+2 best 16 (order 48);
  K3,3 best 6 (order 31).

**Filters are necessary conditions (so pruning is safe).**
- Rank filters use d(G^ab): `AbelianInvariants` in GAP returns the invariants of G/G'. Haar: G = <S> with 1 in S, so
  d(G^ab) <= 2. Lifts: the cotree voltages generate G, so d(G^ab) <= cycle rank (3 for the 2+2 base, 4 for 3+3). Both are
  necessary.
- `abfilt.c: ok_dir` and `hx.c: qdp_ok` (line 73) with `quotient_ok` (line 103) count **non-backtracking label sequences
  with multiplicity** (t != previous label). Repeated images in S-bar are therefore counted correctly. The requirement
  tot[v] >= |G'| per coset holds because the |G'| distinct endpoints in one coset need distinct geodesics, which are distinct
  label sequences. Necessary.
- Haar plan (Delta = 3): S normalised to contain 1, S = {1, s1, s2}, s1 over Aut-orbit representatives and s2 over
  Stab(s1)-orbit representatives. This is complete, since right translation and automorphisms preserve H(G,S).
- Lift plan: the first free voltage ranges over Aut-orbit representatives including the identity. The others range over
  all of G. Parallel edges must have distinct voltages (`lx.c:128`). Lifts are checked from one source per base vertex,
  which suffices because G acts transitively on each fibre by automorphisms.
- **Identity-voltage bug (s.2.5).** The first free edge (file order) is parallel to a tree edge in b22 (0-2), b33_0 (0-5)
  and b33_1 (0-5), so excluding the identity there is harmless. In K3,3 (b33_2) the first free edge 1-4 is not a tree
  edge, so the identity was needed. The `idfix` run is the one that is used. Correct.

**Not re-checked by me (UNVERIFIED):** the BFS code `bfs_cost` in `hx.c` and the lift diameter BFS in `lx.c`. The write-up
says these were validated against igraph (`hx_check_igraph.txt`). I checked the filters and the enumeration logic only.

**Gap B (s.2.5, line 279-280):** "Conder's group C2 x (C7:C3) at order 42 is the only solving group at the table size" is
cited to `runs/lift_b22_D7.tsv`. That file covers orders 43-63 only (`lift_b22.sh`: `allgroups.py 3 7 43 63`). No file in
`runs/` or `verify/` records a 2+2 search at order 42. The 3+3 files contain order 42, but those are not 2+2 runs. This
does not touch the >168 theorem (168 is excluded), but the claim is not supported by the cited evidence.

**Gap C (s.2.5, line 277):** "were searched over every group up to the Moore bound of 254 vertices" is broader than the
runs. They cover exactly 168 < n <= 254 (Haar 85-127, 2+2 43-63, 3+3 29-42). That is what the theorem needs, so the
sentence should say so.

## Process notes

- The brief said no git and only this folder. I created an empty `/tmp/nog.g` by mistake, and it has been deleted.
- One heredoc hung in my own shell, and I killed only that shell and its `cat` child. The other GAP processes running on
  the machine belong to the main session and were not touched.
- GAP was run once for `NrSmallGroups` (light, a few seconds). No other heavy work.

## Files in this folder

- `notes.md` (this file); `nrsg.g`, `nrsg_out.txt`, `nrsg_err.txt` (GAP group counts);
- `check_counts.py` (TSV rows vs GAP per order); `check_bases_costs.py` (base classification, best costs);
- `hom_test.py` (homomorphism test of the universal group, correct vs naive action).
