"""c3: lines opposite to every member of a partial spread (candidates for extending it)."""
import struct, sys
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
with open(HEX, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    LP = [list(struct.unpack('%di' % (q + 1), f.read(4 * (q + 1)))) for _ in range(L)]
PL = [[] for _ in range(N)]
for l in range(L):
    for p in LP[l]:
        PL[p].append(l)
S = [int(x) for x in open(sys.argv[1]).read().split()]
blocked = set()
for R in S:
    blocked.add(R)
    for p in LP[R]:
        for M in PL[p]:
            if M == R: continue
            blocked.add(M)
            for r in LP[M]:
                if r == p: continue
                for L2 in PL[r]:
                    if L2 != M: blocked.add(L2)
free = [x for x in range(L) if x not in blocked]
print('set size', len(S), 'lines not conflicting with any member (extension candidates):', len(free))
print('candidates:', free[:20])
