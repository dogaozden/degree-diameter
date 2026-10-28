"""wg2csr.py: convert a weighted quotient file (orbquot.py format) to the CSR files used by mis3/mcq (weights ignored).
Usage: python3 wg2csr.py IN.wg PREFIX"""
import sys
import numpy as np
tok = open(sys.argv[1]).read().split()
n = int(tok[0]); m = int(tok[n + 1]); E = np.array(tok[n + 2:n + 2 + 2 * m], dtype=np.int64).reshape(m, 2)
nbr = [[] for _ in range(n)]
for a, b in E:
    nbr[a].append(b); nbr[b].append(a)
off = np.zeros(n + 1, dtype=np.int32); off[1:] = np.cumsum([len(x) for x in nbr])
np.array([n], dtype=np.int32).tofile(sys.argv[2] + '_n.bin'); off.tofile(sys.argv[2] + '_off.bin')
np.array([v for x in nbr for v in sorted(x)], dtype=np.int32).tofile(sys.argv[2] + '_nb.bin')
print(n, m)
