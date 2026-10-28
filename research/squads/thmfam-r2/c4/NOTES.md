# c4: LPS(5) x Z_m covers, label search (round thmfam-r2)

Setup: base LPS(5,q) = gen_lps_cover.py 5 q 1 zero (base diam: q=7:6, 11:7, 13:7, 19:8, 23:8, 29:9, 31:10, 37:10).
A cover's diameter is at least its base diameter, so D=8 needs q in {7,11,13,19,23}, D=9 q <= 29 (q=17,29 at D=9).
Harness: cscan.c / cscan2.c (C copy of haar_ecc's PGL BFS; z0=0, z1 fixed to 1 in cscan, searched in cscan2;
hill climbing on f = #vertices beyond distance T from (I,A),(I,B), FULL = both components of size q(q^2-1)m).
Python search.py (slow reference) agrees with cscan on q=11 m=24 at T=8 (both fail).

Results (all cells FULL, none reached the target diameter):
- T=8: (11,24) V=31680 best f=28 (diam 9); (13,14) V=30576 f=14; (19,5) V=34200 f=58; (23,3) V=36432 f=204;
  (11,23) V=30360 f=10. The lab record 31680 at (6,8) was not reproduced at diameter 8.
- T=9: (13,54) V=117936 f=6; (11,89) f=26; (17,24) f=15; (19,18) f=36; (23,10) f=43; (29,5) f=53. No FULL cover at diam 9.
- Only FULL diam-9 cover found: q=11 m=24, labels 0 1 21 21 22 9 (cscan, T=9), V=31680 (this is at diam 9, far below 117360).
- (6,10): not finished (batch stopped on director's request). Table target 452032 not tested.

Score: 0 (no cell beats the 2013 table; no FULL cover reached the target diameter at (6,8) or (6,9)).
Nothing claimed above the table, so no verify_cover re-check was needed.
Budget used: about 2400 hill-climb evaluations per cell at T=8 (6 restarts x 250), fewer at T=9.
