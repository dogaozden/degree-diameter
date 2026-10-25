# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 19:05 UTC, cell-11-10 (Opus, cloud session), round 1: (11,10) above the table

Goal: (Δ, D) = (11, 10). The live wiki table (read over plain HTTP; HTTPS fails certificate checks here) has
130,592,354 (Eyal Loz). Opus before the round: haar_sym (research/structured, copied from branch
claude/structured-search-orbit-04hefm @ 03050f1) with ORBIT="3 3 2" solved SL(2,79) × Z133 (131,127,360) in 9
evaluations and PSL(2,149) × Z43 (142,235,400, μ = 11.7) in 89. At the table μ is only 2.7 (W = 1,111,111,111), so
the cell was open only because our copy of the table could not read it. Calibration: k = 3 0.09 s per evaluation,
k = 5 0.25 s, 1.3–1.4 GB per run at N ≈ 75M. The machine fits 4 heavy runs, so every heavy command went through a CPU-slot
gate (research/squads/d11D10-r1/gate.sh). Squad A = 8 search cards (15 slot-min each), squad B = 8 tool and analysis
cards (0–10 slot-min). Files: research/squads/d11D10-r1/{PREAMBLE.md, CARDS.md, scoreboard.jsonl}.

Cards: A1 k = 5 PSL small p, large n · A2 k = 5 PSL medium p · A3 k = 5 SL · A4 k = 3 PSL on A1/A2's groups ·
A5 k = 3 SL on A3's groups · A6 α pairings (AR/ALPHA) · A7 Frobenius α on SL(2,32) × Z_n · A8 search wildcard ·
B1 second PSL checker · B2 prime-power checker · B3 PGL checker · B4 ball-growth census · B5 speed knobs ·
B6 better orbit moves · B7 theory/plan · B8 open wildcard.

### Round 1 outcomes (best score per card; costs are uncovered elements, μ at the card's group)

- A1 k = 5 PSL small p: no solve. PSL(2,61) × Z661 (μ 27.6) best 5 after 3,857 evaluations. RANDORB-150 medians
  62 / 46 / 91 for PSL(2,41) × Z2161, PSL(2,61) × Z661, PSL(2,41) × Z2201: a large cyclic factor hurts.
- **A2 k = 5 PSL medium p: 148,729,680 VALID** (PSL(2,89) × Z211, μ 24.1, 609 evaluations; haarcheck_psl and pqcheck).
- A3 k = 5 SL: no solve. SL(2,61) × Z331 (μ 28.3) stuck at one uncovered α-fixed element (4,241 evaluations).
- A4 k = 3 PSL: no solve. RANDORB medians are about twice k = 5's on the same groups; PSL(2,127) × Z73 best 3.
- A5 k = 3 SL: screens only (medians 40–66 at μ ≈ 28), no anneal inside the box.
- A6 α pairings: only two of the four AR choices are inequivalent (r ~ r⁴ and r² ~ r³, a Weyl element inverts g), as
  predicted; medians 42 vs 46 at 200 samples; the anneal stopped at two α-fixed elements.
- A7 Frobenius α on SL(2,32) × Z_n: worse (median 110 at μ 31.7; small Q, n ≈ 2,300).
- A8 one α-orbit of size 11 (k = 11, f = 0) on PSL(2,23) × Z12409: hopeless (RANDORB minimum 10,884 at μ 29.7).
- B1 second PSL checker (pslcheck_b1): validated; 142,235,400 VALID.
- B2 prime-power checker (haarcheck_pq): agrees with build_haar2.py on 17/17 files.
- B3 PGL checker: see its folder (report pending at the time of writing).
- B4 ball-growth census: typical samples grow like random words to level 8; the excess cost comes from a tail of
  degenerate S.
- B5 speed: FAST=1 is about 1.25× faster than the default on PSL(2,101) × Z151 (re-measured by Opus: 0.19 vs 0.21 s per
  evaluation; identical trace hash); on PSL(2,243) × Z11 the default is 2× faster.
- B6 better orbit moves: see its folder.
- B7 plan: recommended PSL(2,41) × Z2251 from the model; the measured screens contradict it (large n).
- B8 metacyclic Z_p ⋊ Z5: not screened (slow evaluation path, gate timeout).

Kept: k = 5 with large |Q| and small n (PSL(2,89) × Z211, PSL(2,101) × Z151), and Frobenius α on PSL(2,243) × Z11 (Opus
screen: median 66 at μ 60.6, the best ratio to μ of any group, 11 α-fixed elements). Opus runs after the round:
PSL(2,101) × Z151 (155.6M, μ 48.6) reached two uncovered α-fixed elements after 3,601 evaluations and is being
continued from its checkpoint plus a second seed; PSL(2,243) × Z11 (157.8M) runs alongside.
Opus wrote research/squads/d11D10-r1/opus/pqcheck.c, a third independent checker (SL/PSL over any GF(q)).

## 2026-10-25 12:55 UTC, cell-11-10 resumed (Opus, cloud session), round 2: PSL(2,243) × Z11 (157.8M)

The first session (round 1, 148,729,680 vertices) was cut off by the usage limit; its two long runs were lost (no
checkpoints were committed). This session works on branch claude/cell-11-10-resume-oubzk2 and commits checkpoints.
New in haar_sym: `AFROBH` / `AFROBD` (conjugation by a GF(3)-rational involution after the Frobenius of GF(3^5), giving an
automorphism of order 10 of PSL(2,243) × Z11 with z ↦ 2z; Fix = 3 or 1 elements), so ORBIT="10 1 1" (S = {e} ∪ one
orbit of size 10, clumps of 10, μ/10 = 6.1); `RANDB` / `RANDSTOP` turn RANDORB into a random search.
Files: research/squads/d11D10-r2/{PREAMBLE.md, CARDS.md, scoreboard.jsonl}.

Cards: A1 k = 10 pairing screen · A2 degenerate k = 10 samples · A3 k = 5 Frobenius anneal AFROB=2 · A4 k = 5 AFROB=4
other schedule · A5 outer involution AFROBD · A6 conjugation-family fallbacks (150.7M, 153.3M) · A7 other groups ·
A8 open wildcard · B1 small-orbit prefilter · B2 speed of a k = 10 sample · B3 theory of the k = 10 excess ·
B4 prime-power checkers · B5 ball census · B6 cost by class of the orbit generator · B7 tools wildcard ·
B8 constructions wildcard.

### Round 2 outcomes (best score per card; costs are uncovered elements of psl 243 × Z11, μ = 60.6, unless stated)

- A1 k = 10 pairings (z ↦ 2z): the four Frobenius powers are inequivalent but tie in the bulk (median ≈ 100 = 10
  clumps); 13 % degenerate. AR = 6/7 reproduce AFROB = 4/3. Lowest 20.
- A2 degenerate samples: exactly the orbit generators with z = 0 (S inside PSL(2,243) × {0}, cost 71,743,320); `SKIPZ=1`.
- A3 k = 5 AFROB=2 anneal: never got a gate slot (the gate has no queue; polling jobs starve).
- A4 k = 5 AFROB=4 anneal: cost 20 at 31 s, never improved (RESTART never fired: REHEATSTEPS 400 > 130 steps).
- A5 outer involution AFROBD (z ↦ 2z): same bulk as AFROBH (mean ≈ 10 clumps), one sample at cost 10.
- A6 conjugation fallbacks: psl 71 × Z421 (150.65M) cost 5, psl 79 × Z311 (153.3M) cost 10, 330 s each.
- A7 other groups: PSL(2,32) × Z2281 mixes badly (median 3.1 μ); heis 191 × Z11 and k = 10 on PSL(2,32) × Z2281 degenerate.
- A8 twisted Z11-layer orbit S = {(g^k u^−k, k)}: loses about 31 % of its words (min cost 1,870). Dead end. (Its cleanup
  of "until grep" loops also killed other cards' wait loops.)
- B1 small-orbit prefilter `PREF=1` by meet in the middle: 0 mismatches against the BFS on 55 targets × 100 samples.
- B2 speed: a k = 10 sample is 43 % table builds (10 × 22.5 ms) and 57 % BFS; HUGEPG=1 FAST=2 PFD=8 is about 11 % faster.
- B3 theory: no formal word identities up to length 7; the k = 10 excess comes from generator-specific short coincidences.
- B4 checkers: haarcheck_pq and pqcheck agree on psl 243 test files (2 valid, 2 corrupted); 62–86 s at 157.8M.
- B5 ball census: k = 10 with z ↦ 2z falls behind k = 5 from BFS level 4 (−1.1 to −1.5 % at levels 6–8).
- B6 cost by class of the generator: no data (unquoted env var in its script).
- **B7 census + RANDORB: z ↦ 3z (order 5) instead of z ↦ 2z cuts the k = 10 bulk from 9.5 to 7.7 clumps.** This was
  the idea that won.
- B8 constructions: no non-search route above 148.7M (abelian/bi-circulant ≤ 907,753 per side; blow-ups and lifts far off).

Opus: screened B7's lead at 200 samples (AFROBH and AFROBD with z ↦ 3z: medians 75 and 74 against 100–111; AFROBD had a
cost-1 sample), merged B1's PREF and A2's SKIPZ into haar_sym (0.22 s per sample instead of 0.45 s), and ran three
seeds of `ORBIT="10 1 1" AFROB=j AFROBD=1 AR=3 SKIPZ=1 PREF=1 PREFMAX=2 RANDB=1 RANDSTOP=1`. Seed 201 hit cost 0 at sample
751 (165 s): **157,835,304 vertices** (PSL(2,243) × Z11), VALID in haarcheck_pq and pqcheck, +20.9 % over the table,
+6.1 % over round 1. Squad value this round: high. Three cards (B7, A2, B1) supplied the three ingredients of the solve
within 30 minutes; Opus's own k = 5 Frobenius anneal (48 min, cost 15) and k = 10 z ↦ 2z random search (7,000 samples)
found nothing. Stopped here: no group with this structure exists between 78.9M and the about 81M that the method could
still reach (research/squads/cells/d11D10.md, last section).
