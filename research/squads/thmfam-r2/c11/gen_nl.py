#!/usr/bin/env python3
"""c11: nonlinear equivariant label rules for LPS x Z_m covers.
Generator lines "a b c d z" as in gen_lps_cover.py (same psi(alpha), same S_p representatives, same r).
Family: z(alpha) = sum_{k=1..3} F(a_k) r^(k-1) mod m  (slot-symmetric, so z(sigma alpha) = r z(alpha) exactly on the
quaternion), or coupled: z = sum_k F(a0, a_k) r^(k-1).  Any F is an equivariant rule.  Fixed letters a1=a2=a3 get
F(a)(1+r+r^2) = 0.  Constant or a0-free additive shifts of F vanish, so F(a)+c and F(a)+a0 equal F(a) (see NOTES.md).
Usage: gen_nl.py p q m RULE   (prints p+1 lines)."""
import sys, math
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r2/c11')
from gen_lps_cover import lps_set  # noqa  (module-level main() is guarded below)
