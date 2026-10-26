# Verification card v1 (round f65r2): Heis(7), |S| = 6

Claim checked: min over 6-subsets S of G = Heis(7) of |G \ (S^-1 S)^2| equals 4 (no S covers G).

## Result
- Minimum number of uncovered elements: **4** (agrees with the director's 4).
- Sets checked (reduced enumeration): 84,408,740 (13 orbit representatives x C(340,3) = 6,492,980 each).
- Representative sets attaining the minimum: 1800 (counted within the reduced enumeration, not the full space).
- Any set covering everything: **no**.
- Witness with 4 uncovered: S = {(0,0,0), (1,0,0), (0,1,0), (0,2,2), (1,2,1), (4,4,2)}; uncovered = (0,2,3), (0,5,4), (2,1,6), (5,6,3).
  Re-checked with an independent Python script (`witness_check.py`, same folder): 4 uncovered, as the C code reports.
- Run time: 189 s wall (3 min 9 s real, 78 s user; shared machine at load about 9-13 on 4 cores).

## Method
- Group: elements (a,b,c) mod 7, product (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'). Index = 49a + 7b + c.
- Multiplication and inverse tables precomputed. For each S: Q = {x^-1 y : x,y in S} (at most 31 elements),
  covered set = {q q' : q, q' in Q} stored in a 343-bit bitset (6 words), uncovered = 343 - popcount.
- Automorphisms, generated explicitly rather than assumed: phi(a,b,c) = (M(a,b), det(M)(c + al*a + be*b) + Q(a,b)),
  M in GL(2,7), al, be in F_7, with Q(u) = D(u,u)/2 and D(u,v) = (Mu)_1(Mv)_2 - det(M) u_1 v_2 - (symmetrisation).
  Each candidate was verified to be an automorphism (bijective, and phi(s g) = phi(s) phi(g) for generators s = x, y and all g,
  which suffices). All 98,784 = 49 x 2016 candidates passed; none rejected.
- Transitivity checked numerically: orbit of (1,0,0) = 336 (all noncentral), orbit of (0,0,1) = 6 (all nontrivial central).
- Normalisation (each step preserves the uncovered count):
  (i) right translation S -> S g^-1 maps (S^-1S)^2 to a conjugate by g, so the count is unchanged; WLOG e in S.
  (ii) if S has a noncentral element t, an automorphism sends t to (1,0,0). If all of S\{e} is central, covered set lies in
      the centre (7 elements) and uncovered >= 336, so this case is irrelevant. WLOG (1,0,0) in S.
  (iii) H = Stab_Aut((1,0,0)), |H| = 294 (checked). H has 13 orbits on G \ {e, (1,0,0)}; WLOG S contains one orbit
      representative r (orbits: (0,0,1), (0,1,0), (1,0,1), (2,0,0), (2,0,1), (3,0,0), (3,0,1), (4,0,0), (4,0,1), (5,0,0),
      (5,0,1), (6,0,0), (6,0,1)). The other 3 elements range over all triples from the remaining 340 elements.
- Reduction validated on Heis(3) by comparing with full enumeration of all 6-subsets (and all |S| = 3, 4, 5 cases):
  minima agree (|S|=3: 8 vs 8; |S|=4: 0 vs 0; |S|=5: 0 vs 0; |S|=6: 0 vs 0). Same program with `full` mode on Heis(3) at |S|=6
  enumerates 65,780 sets (all with e in S) and reports min 0 (so "covers everything" is detected).
- Cyclic Z_20 sanity case (full enumeration, 11,628 sets): min 0, reported correctly.

## Files
- Code: /home/user/degree-diameter/research/squads/f65r2/v1/heis_cover.c (binary heis_cover)
  usage: `./heis_cover heis 7 reduced 6` (full mode also available for small p; `cyc N` for cyclic groups).
- Output: /home/user/degree-diameter/research/squads/f65r2/v1/run_heis7_k6.txt
- Independent witness check: /home/user/degree-diameter/research/squads/f65r2/v1/witness_check.py

## Notes
- The 1800 "attaining" count is over reduced representatives and is not the full count of minimisers in the unreduced space.
- The unreduced space (about 3.9e10 sets containing e) was not enumerated; the claim relies on the automorphism/translation reduction above,
  which was validated on Heis(3) as described.
- The director's code in research/fresh65/tools/ was not read or reused.
