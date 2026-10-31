# c18 notes (card: Haar graphs with hub orbits, types "1,k|1,k", mcos)

## Model (checked by hand)
Type "1,k|1,k": A = A0 (regular, |G|) + A1 (hub orbit G/H, |H| = k); B = B0 (regular) + B1 (hub).
Blocks n_ab (double cosets per block, from mcos's degree rule): n00 + n01 = 6 (A0), 6(n10+n11) = 6 (A1),
n00 + n10 = 6 (B0), n01 + n11 = 1 (B1) for k = 6. Solutions: n11 = 1 (disconnected: A0+B0 and A1+B1 split) or
n11 = 0, n00 = 5, n01 = n10 = 1 (the connected one). So N="5,1,1,0" (row-major: (A0,B0),(A0,B1),(A1,B0),(A1,B1)).
n = 2|G| + 2|G|/k = 7|G|/3 for k = 6; needs 6 | |G| and an element of order 6 (cyclic stabiliser for mcos).
Other k: "1,3|1,3" n = 8|G|/3 (|G| >= 258, 3 | |G|), "1,2|1,2" n = 3|G| (|G| >= 230), "1,4|1,4" n = 5|G|/2 (|G| >= 276).

## Tools
- Group tables: GAP from shared/gap_tables.g into c18/groups (orders 294, 300, 306, 312 generated; c5 has only 342-380).
- c18/has6.py TABLE...: counts element orders (which groups have order-6 elements).
- c18/screen.sh TYPE N SECS SEED DEADLINE TABLE...: mcos on each group, appends scan/<TAG>.tsv (group, name, type, N, best, sec).
- Calibration: TYPE "1|1" on SmallGroup(342,12), SEED 4, 22 s -> cost 0 (684 Haar graph, check.sh VALID). SEED 2 and 3 stalled at 4 in 30 s.
- Note: the bash tool has a 120 s limit by default; pass timeout 300000 explicitly or the job gets backgrounded.

## Results
- 1,6|1,6 N=5,1,1,0: 300_13 (ord6 = 50) 3 s -> cost 53 (n 700). Screen at 8 s per combo, see scan/1-6_1-6-5-1-1-0.tsv.
