# pure-hexagon question: smallest family of points whose radius-4 balls (incidence distance) cover all points
import struct, random
data = open('hex/hex_q5.bin','rb').read()
q, N, _ = struct.unpack('<iii', data[:12]); Q1 = q+1
LP = struct.unpack('<%di' % (N*Q1), data[12:12+4*N*Q1])
PL = [[] for _ in range(N)]
for l in range(N):
    for k in range(Q1): PL[LP[l*Q1+k]].append(l)
def ball4(p):
    # points within incidence distance 4 of point p (collinearity distance <= 2)
    seen_p = {p}; lines = set(PL[p]); frontier = set(lines)
    pts = {p}
    for l in lines:
        for x in [LP[l*Q1+k] for k in range(Q1)]: pts.add(x)
    lines2 = set()
    for x in list(pts):
        for l in PL[x]:
            if l not in lines: lines2.add(l)
    for l in lines2:
        for k in range(Q1): pts.add(LP[l*Q1+k])
    return pts
balls = [0]*N
for p in range(N):
    m = 0
    for x in ball4(p): m |= 1 << x
    balls[p] = m
print('ball sizes', min(bin(b).count('1') for b in balls), max(bin(b).count('1') for b in balls), flush=True)
full = (1 << N) - 1
best = None
for trial in range(30):
    rnd = random.Random(trial); unc = full; chosen = []
    while unc:
        # greedy with random tie-break among near-best
        cand = sorted(range(N), key=lambda p: -bin(balls[p] & unc).count('1') + rnd.random()*3)[:5]
        p = cand[0] if trial % 2 == 0 else rnd.choice(cand)
        chosen.append(p); unc &= ~balls[p]
    if best is None or len(chosen) < len(best): best = chosen
print('best greedy cover size over 30 trials (hexagon 4-balls only):', len(best), flush=True)
