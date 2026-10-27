# c8: small-case checks of the LPS theorems (round thmfam-r1)

Files: checkA.py (part A, own quaternion enumeration and PGL normalisation; partA_log.txt is its output, `--allsol` also tests all sqrt(-1) choices),
lps_haar_sidefix.c (copy of lps_haar.c that keeps the A-side and B-side distances apart; side_p_q.txt outputs),
B_raw_p_q.txt (stock lps_haar outputs), C/ (edge lists g_*.txt, e_*.txt, apsp binary, component_edges.py).

(A) 153 pairs (p in 3..29, primes q<=61, q!=p). Failing pairs: 16, all degenerate:
 - q=2 (9 pairs): psi(1+i+j+k) has det 4 = 0 mod 2, so h is not in PGL(2,2); the image of S_p collapses to 1 element.
 - q=3, p in {11,13,17,19,23,29} (6 pairs) and q=5, p=29 (1 pair): psi is not injective on S_p (6 to 12 distinct classes), so the conjugation is not a permutation.
 - Every other pair (q>=7, plus q=3,5 with small p) gives p+1 distinct elements, closure under conj by h, cycle type as predicted, ord(h)=3.
 - Predicted cycle types match exactly on all clean pairs.

(B) 41 pairs (p=5,7 with q=1 mod 4 up to 113; p=11,13 up to 61).
 - With d = d((e,A),(psi(i),A)) (A-side distance), bound 4 log_p q - 2 log_p 2 holds in 41/41, and d = least even L with 2 p^(L/2) >= q^2-1 in 41/41.
 - Bug in lps_haar.c: the single dist[] array is written by both sides of the bipartite BFS, so the printed d(e,psi(i)) equals max(d_A, d_B) when (psi(i),B) is also reached. This happens for 7 pairs: (7,37), (7,53), (7,109), (11,37), (13,17), (13,53), (13,61); stock prints 9,9,11,7,5,7,7 against the true 8,8,10,6,4,6,6.

(C) 6 graphs (p=5 q=13,17; p=7 q=11,13; p=13 q=17; p=3 q=17): apsp diameter = haar_ecc diameter in 6/6 (7, 9, 6, 6, 7, 11).
Also: my psi image equals lps_haar's image (as PGL sets, normalised) for all 136 (p,q) pairs tested.
