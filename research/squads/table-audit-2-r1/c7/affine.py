#!/usr/bin/env python3
"""c7: independent affine orbit maps for points and lines per copy (closed form, no search).
P_c(g^j p_s) = g^j p_{(u_c s + v_c) mod 126},  L_c(g^j l_s) = g^j l_{(w_c s + z_c) mod 126},
u_c, w_c units mod 126 chosen from sweep.UNITS by c*k + offset; v_c = c*kv, z_c = c*kz."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sweep as S
U = S.UNITS; R = S.R
def fam(k1, k2, k3, kv, kz):
    def fn(c, s):
        u = U[(c * k1) % len(U)]; w = U[(c * k2 + k3) % len(U)]
        return ((u * s + c * kv) % R, 0, (w * s + c * kz) % R, 0)
    return fn
if __name__ == '__main__':
    res = []
    for combo in sys.argv[1:]:
        k1, k2, k3, kv, kz = map(int, combo.split(':'))
        res.append(S.run(f'aff_{k1}_{k2}_{k3}_{kv}_{kz}', 'abab', 'LLLL', fam(k1, k2, k3, kv, kz)))
    if res: print('BEST', min(res))
