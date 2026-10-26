#!/usr/bin/env python3
# apply.py C0_IN.lift2.sol OUT.lift2.sol flip1 flip2 ... : nu (line 7 = 3*nu) with the listed flags toggled.
import sys
src, out, flips = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3:]]
lines = open(src).read().split('\n')
nu = [int(x) // 3 for x in lines[6].split()]
for f in flips: nu[f] ^= 1
lines[6] = ' '.join(str(3 * v) for v in nu)
open(out, 'w').write('\n'.join(lines))
print('wrote', out, 'flips', flips)
