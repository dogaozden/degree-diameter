# Squad d16D10-r1: the 8 cards (proxy (16,8), |G| ≈ 13–14M; preamble in PREAMBLE.md)

c1. Calibration curve. Main recipe ORBIT="3 5 1" on SL(2,p) × Z_n. Pick ~6 groups with μ ≈ 10, 14, 18, 22, 26, 30
    (use orb_screen.py --list with --fams sl), 2 seeds each, ≤ 240 s per run. Fit log(evals) = a + b·μ over the solved
    runs (unsolved: record best cost). Score = b (lower = effort grows slower with μ). Report a, b and the largest μ solved.

c2. Group shape at fixed μ. Is a large cyclic factor good or bad? ORBIT="3 5 1" on SL(2,p) × Z_n at μ ≈ 16–22 with
    n = 1, n small (7–19), n medium (~40–100) and n large (~200–300) (e.g. sl 239 n 1, sl 101 n 13, sl 53 n 91,
    sl 41 n 199, sl 37 n 271; check μ with orb_screen.py --list). 3 seeds each, ≤ 200 s. Score = best E18; say which
    shape is best and by how much.

c3. Base group type. SL(2,p) vs PSL(2,p) vs PGL(2,p) (× Z_n) at μ ≈ 16–22, ORBIT="3 5 1", 3 seeds each, ≤ 200 s.
    Use groups of similar n so only the type differs. Score = best E18; rank the three types.

c4. Search parameters for a small evaluation budget. On sl 53 × Z91 (μ 18.25) with ORBIT="3 5 1", vary one at a time:
    K ∈ {4, 8, 16}; TARGP ∈ {40, 70, 95}; TMAX/TMIN (default 1.5/0.15) ∈ {0.8/0.08, 3/0.3}; RESTART=1; COOL (default
    20 s; note COOL/REHEAT are wall-clock seconds, so also try VCLOCK=0.01 with COOL=2 to make it eval-based). 3–4
    seeds each, ≤ 120 s. Score = best E18 (median evals); report the best setting vs the default.

c5. Independent fast checker. Write a NEW C program (OpenMP), from the definitions only, that checks the diameter of
    H(G,S), G = SL(2,p) × Z_n, p prime, read from a solution file (format: header `d D sl p n NCYC N NTOT`, then d lines
    `<idx> mat(a,b,c,d) z=Z`; edges (g,A) ~ (s g, B); BFS from (e,A) and (e,B) to depth D must reach all 2N vertices).
    Must use 64-bit element indices (N up to 2.4·10⁹) and ≤ 4 bits of RAM per element. Validate: VALID on
    research/frontier/sols/d10D9_sl_83_7_orb3_s1.txt, d11D9_sl_61_37_orb3_s1.txt, d10D10_sl_79_61_orb3_s1.txt; INVALID
    on copies where one generator's z is changed by 1 and where D in the header is lowered by 1; compare with
    $T/tools/hcsl (the existing checker, same file argument). Score = projected seconds for N = 2.2·10⁹ with 2
    threads (from your timings; lower is better); valid = agreed with hcsl on all tests. Put code in c5/.

c6. Wildcard: other group families at μ ≈ 16–22 with ORBIT="3 5 1" (or the k, m, f that fits): products
    (`prod sl 5 sl 9`, `prod psl 7 sl 16`, ...), prime-power fields (sl 49, sl 81, psl 125 ...), or anything in
    haar_sym's GROUP list not used by c2/c3. 2–3 seeds each. Score = best E18; compare with the sl 53 × Z91 reference.

c7. Wildcard: α and orbit variants on sl 53 × Z91 (μ 18.25) and one PSL group: ORBIT="3 4 4" (e + 3 fixed torus
    generators + 4 orbits) vs "3 5 1"; ORBW=3; AR override (a z ↦ rz with fixed points); ALPHA override with a
    conjugating element from the other torus (p ≡ 1 vs 2 mod 3 decides which torus the default uses: compare a
    p ≡ 1 mod 3 group with a p ≡ 2 mod 3 group at equal μ). Score = best E18.

c8. Wildcard: an approach none of c1–c7 uses (they cover: μ calibration, group shape, SL/PSL/PGL, annealing params,
    a checker, other group families, α/orbit variants). Write it as code or a concrete command plan and score it on
    the proxy with E18. Ideas if you need one: a new move (replace one element of an orbit's generator by a nearby
    element, i.e. multiply by a short word), recombining orbits from two good S, tabu list of recently used orbits,
    restarts seeded from the best RANDORB sample. Keep it to one idea, done properly.
