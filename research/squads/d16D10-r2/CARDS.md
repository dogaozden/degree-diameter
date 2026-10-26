# Squad d16D10-r2: cards

Band: (16,10), |G| in [2.30e9, 2.32e9], μ ≈ 38–41. Score: best cost after one 600 s run (0 = record candidate).
Default schedule unless the card says otherwise: K = 4, TARGP 70, TMAX 1.5, TMIN 0.15, COOLSTEPS 4, REHEATSTEPS 60.

- c1 (tiny p, huge n): PSL(2,31) × Z154571, ORBIT="5 3 1" (μ 38.4, 15 fixed elements). Is a nearly cyclic group OK?
- c2 (SL, mid p): SL(2,61) × Z10141, ORBIT="5 3 1" (μ 38.8, 60 fixed elements).
- c3 (PSL, mid p; the baseline for c6 and c7): PSL(2,71) × Z12871, ORBIT="5 3 1" (μ 39.3, 35 fixed).
- c4 (large p, small n): PSL(2,191) × Z661, ORBIT="5 3 1" (μ 39.3, 95 fixed).
- c5 (k = 3 against k = 5): PSL(2,61) × Z20287, ORBIT="3 5 1" (μ 38.9; k = 3 fixed holes are negligible but μ/3 free
  hole orbits instead of μ/5).
- c6 (schedule): PSL(2,71) × Z12871, ORBIT="5 3 1", one schedule change of your choice with a stated reason (e.g. TMIN
  0.5 to keep exploring at low cost, K = 8, TARGP = 100 or 30, REHEATSTEPS = 10, COOLSTEPS = 12).
- c7 (restarts): PSL(2,71) × Z12871, ORBIT="5 3 1", three 200 s runs with seeds 11, 12, 13 inside ONE slot
  (`$R/slot.sh c7 bash -c 'for s in 11 12 13; do timeout 230 nice -n 10 $HB 16 10 200 $s 4 out_s$s.txt psl 71 12871 > s$s.out 2> s$s.log; done'`).
  Score = best of the three.
- c8 (wildcard): an approach none of c1–c7 uses, inside the band and with this tool. Not used by c1–c7: other α
  choices (AT, AR), other k (k = 15, m = 1: needs p ≡ ±1 mod 15 and n with prime factors ≡ 1 mod 15), the SL family
  at small p, SL(2,p) with n = 1 (p ≈ 1321), K = 1 or 2, a START from your own first run's .best with a new seed.
