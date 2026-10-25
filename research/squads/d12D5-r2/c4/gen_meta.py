#!/usr/bin/env python3
"""All metacyclic groups Z_M x| Z_K (x,y)(x',y') = (x + R^y x', y + y') of order 70..84 with R != 1, R^K = 1 mod M."""
import math, os
out = []
for n in range(70, 85):
    for K in range(2, n):
        if n % K: continue
        M = n // K
        if M < 3: continue
        for R in range(2, M):
            if math.gcd(R, M) != 1 or pow(R, K, M) != 1 % M: continue
            # (x,y) index: y*M + x
            N = M * K
            pw = [pow(R, y, M) for y in range(K)]
            T = [[0] * N for _ in range(N)]
            for y1 in range(K):
                for x1 in range(M):
                    a = y1 * M + x1
                    for y2 in range(K):
                        for x2 in range(M):
                            b = y2 * M + x2
                            T[a][b] = ((y1 + y2) % K) * M + (x1 + pw[y1] * x2) % M
            name = f'meta_{M}_{K}_{R}'
            with open(f'tables2/{name}.txt', 'w') as f:
                f.write(f"{N}\n" + ' '.join(str(x) for row in T for x in row) + '\n')
            out.append((N, name))
print(len(out), 'groups')
print(' '.join(name for _, name in out))
