#!/bin/sh
# Referee checks of research/paper/joint.tex (draft of 28 Oct 2026). Needs python3 with sympy, gcc with OpenMP.
# Usage: sh run_all.sh > run.log 2>&1   (about 3 minutes; the q=7 and q=8 hexagon runs take longer, see d6_q7.log, d6even_q8.log)
set -e
gcc -O2 -fopenmp -o apsp64 apsp64.c
chk() { printf '%s: ' "$1"; ./apsp64 < "$1.edges"; }
echo "== Section 3 (fourth hat)"; python3 hat4_ref.py; python3 hat4_free.py
echo "== Section 4.2 (AS(q))"; python3 as_ref.py; for q in 3 5 7 9; do chk as_cor48_q$q; done
echo "== Section 4.3 (Singer 2-ovoids)"; python3 singer_ref.py 3 5 7; for q in 3 5 7; do chk singer_cor411_q$q; chk singer_cor411_q${q}_reg; done
echo "== Appendix A"; python3 app359_ref.py; chk app359
echo "== H(q) from Tits' equations"; python3 hex_basic.py 2 3 4 5; for q in 2 3 4 5; do chk H$q; done
echo "== Section 5 identities (symbolic)"; python3 jz_sym.py; python3 jz_conj.py
echo "== Section 5 (odd q)"; python3 d6_ref.py 3 5; chk d6_q3_m2; chk d6_q3_m3; chk d6_q5_m2
echo "== Section 5.5 and Appendix B (even q)"; python3 d6_even.py 2 4; chk d6even_q2_m2; chk d6even_q4_m2
echo "== Theorem 5.18"; python3 thmR_ref.py 3,2 3,3 5,2; chk thmR_q3_m2; chk thmR_q3_m3; chk thmR_q5_m2
echo "== Corollary 6.20"; python3 d7_ref.py 4 5 5c; chk d7_cor619_q4; chk d7_cor619_q5; chk d7_cor619_q5_control
echo "== Section 7 lemmas, Fact 7.14"; python3 d8_lemmas.py; python3 perp_ref.py
echo "== Omega_q (Definition 7.1) with the thesis labelling"; python3 omega_ref.py 2,ab,1 2,ab,2 2,aa,2 3,aab,1 3,abb,2 3,aaa,2 3,bbb,1
for f in omega_q2_ab_r1 omega_q2_ab_r2 omega_q2_aa_r2 omega_q3_aab_r1 omega_q3_abb_r2 omega_q3_aaa_r2 omega_q3_bbb_r1; do chk $f; done
echo "== Section 8"; python3 haar_ref.py
echo "== Tables"; python3 tables_ref.py
