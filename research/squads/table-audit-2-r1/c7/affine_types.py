import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sweep as S, affine as A
res = []
for types, inner, combo in [('abab','PPPP','7:5:3:11:29'), ('abab','LPLP','7:5:3:11:29'),
                            ('abba','LLLL','7:5:3:11:29'), ('abab','LLLL','7:5:3:13:23'),
                            ('abab','LLLL','7:5:3:5:17')]:
    k1, k2, k3, kv, kz = map(int, combo.split(':'))
    res.append(S.run(f'aff_{types}_{inner}_{kv}_{kz}', types, inner, A.fam(k1, k2, k3, kv, kz)))
print('BEST', min(res))
