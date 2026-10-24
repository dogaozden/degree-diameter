# Opus tools for round d11D10-r1

- `pqcheck.c`: independent low-memory checker for Haar graphs over SL(2,q) x Z_n and PSL(2,q) x Z_n, q any prime power
  (own GF(q) arithmetic from the header polynomial, own PSL canonical form). Build `cc -O3 -o pqcheck pqcheck.c`,
  run `pqcheck SOL.txt` (last line VALID/INVALID with both eccentricities).
- Validation (2026-10-24): VALID on research/frontier/sols/{d11D8_psl_59_11_orb5_ORBW5_s3, d13D8_sl_64_13_orb3_s1,
  d10D9_sl_81_7_s111, d11D9_sl_125_4_s111}.txt; agrees with build_haar2.py on t_psl27.txt, t_psl25_3.txt, t_psl49.txt
  (VALID) and on t_psl49_D6.txt, t_psl25_3_D6.txt (INVALID, eccentricity 7 > 6); rejects t_psl49_bad.txt (an entry
  swap, determinant != 1), c1.txt (one z changed: eccentricity 9 > 8) and c2.txt (repeated generator).
