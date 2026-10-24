# B2: haarcheck_pq (low-memory exact check of Haar graphs over SL/PSL(2, p^e) x Z_n)

Usage: `./haarcheck_pq SOLUTION.txt` (build: `gcc -O2 -o haarcheck_pq haarcheck_pq.c`). Reads a haar_sym solution file (header `d D sl|psl q [poly f] n NCYC N NTOT`, then d lines `i mat(a,b,c,d) z=Z`), runs one bitset BFS from (e,A) and one from (e,B), and prints a last line `VALID d=.. D=.. vertices=.. eccA=.. eccB=..` or `INVALID ...` (exit 0 iff VALID). Memory is about 4|G| bits (|G| = |SL| or |PSL| times n).
