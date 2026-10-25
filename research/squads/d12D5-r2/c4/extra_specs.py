import sys
sys.argv = ['x']
from gen_groups import SPECS, build
from groups import parse, check
EXTRA = {
 's4z3': 'prod perm 1,0,2,3;1,2,3,0 / cyc 3',
 'd4z9': 'prod dih 4 / cyc 9',
 'q8z9': 'prod dicyc 2 / cyc 9',
 'd4z10': 'prod dih 4 / cyc 10',
 'q8z10': 'prod dicyc 2 / cyc 10',
 'z2z2m3_6': 'prod cyc 2 / prod cyc 2 / meta 3 6 2',
 'z2d3z2': 'prod cyc 2 / prod dih 3 / cyc 2',
}
import os
for name, spec in EXTRA.items():
    T = parse(spec.split()); n = len(T); check(T)
    print(name, n, flush=True)
    if 70 <= n <= 84:
        with open(f'tables2/x_{name}.txt', 'w') as f:
            f.write(f"{n}\n" + ' '.join(str(x) for row in T for x in row) + '\n')
