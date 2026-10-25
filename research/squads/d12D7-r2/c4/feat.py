# features of candidate points: incidence/distance in H(9) between p and M(p), F-collinearity counts
import struct, sys, collections
N = 66430; q = 9; Q1 = 10
data = open('hex/hex_q9.bin','rb').read()
q_, N_, L_ = struct.unpack('3i', data[:12])
LP = struct.unpack('%di' % (L_*Q1), data[12:12+4*L_*Q1])
lines_of = [[] for _ in range(N)]
for l in range(L_):
    for t in range(Q1):
        lines_of[LP[l*Q1+t]].append(l)
F = set(map(int, open('/home/user/degree-diameter/research/squads/d12D7/sets/F9_spread730_7300.txt').read().split()))
sol = open('/home/user/degree-diameter/research/frontier/sols/d12D7_hex9_spread730_clhaarPSL9x40_n693100.sol').read().split()
K = int(sol[3]); i = 6 + K + 2
M = list(map(int, sol[i:i+N]))
assert len(M) == N
def pts_of(l): return LP[l*Q1:(l+1)*Q1]
def dist_point_line(p, target_line, maxd=7):
    # BFS in incidence graph from point p (nodes: ('p',x) and ('l',y)); return distance
    seen_p = {p}; seen_l = set(); frontier = [('p', p)]; d = 0
    while frontier and d < maxd:
        d += 1; nxt = []
        for typ, x in frontier:
            if typ == 'p':
                for l in lines_of[x]:
                    if l not in seen_l:
                        seen_l.add(l); nxt.append(('l', l))
            else:
                for y in pts_of(x):
                    if y not in seen_p:
                        seen_p.add(y); nxt.append(('p', y))
        frontier = nxt
        if ('l', target_line) in [(t, x) for t, x in frontier]:
            return d
    return -1
def feats(p):
    lines = lines_of[p]
    fcol = set()
    for l in lines:
        for y in pts_of(l):
            if y in F and y != p: fcol.add(y)
    nF_lines = sum(1 for l in lines if any(y in F for y in pts_of(l)))
    inc = 1 if M[p] in lines else 0
    d = dist_point_line(p, M[p], 7) if not inc else 1
    return dict(p=p, inc=inc, dist=d, collF=len(fcol), linesWithF=nF_lines, M_inF_lines=int(M[p] in [l for l in lines]))
if __name__ == '__main__':
    pts = [int(x) for x in sys.argv[1:]]
    for p in pts:
        print(feats(p))
