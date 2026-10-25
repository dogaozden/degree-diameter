"""flaggreedy.py GQBIN SEED TRIES [SOLIN]: grow a set of freed flags (p in l = sigma(p)) while the exact-coverage
matching problem (see flagmatch.py) still has a perfect matching.  Bitset version.  Prints the flags and, for the
final set, writes sigma (kept close to SOLIN's sigma where allowed) to stdout as 'SIGMA ...'."""
import sys, random
sys.path.insert(0, '.')
from gq import load, perp, lperp

q, N, lines, lof = load(sys.argv[1]); seed = int(sys.argv[2]); tries = int(sys.argv[3])
rng = random.Random(seed)
sig0 = None
if len(sys.argv) > 4:
    tok = open(sys.argv[4]).read().split(); sig0 = list(map(int, tok[7:7 + N]))
Pm = [sum(1 << y for y in perp(lines, lof, p)) for p in range(N)]          # point perps (incl. p)
Lm = [sum(1 << m for m in lperp(lines, lof, l)) for l in range(N)]         # line perps (incl. l)
onl = [sum(1 << y for y in lines[l]) for l in range(N)]                    # points on l
thr = [sum(1 << m for m in lof[p]) for p in range(N)]                      # lines through p
ALL = (1 << N) - 1

def matching(flags):
    F = {p: l for p, l in flags}; Fl = {l for p, l in flags}
    Fm = sum(1 << p for p in F); Flm = sum(1 << l for l in Fl)
    lineok = [ALL & ~Flm] * N        # for point x: allowed lines
    ptok = [ALL & ~Fm] * N           # for line M: allowed points
    for p, l in flags:
        A = Pm[p] & ~onl[l]; G = Lm[l] & ~thr[p]
        Ll = Lm[l] & ~(1 << l); Pp = Pm[p] & ~(1 << p)
        x = A
        while x:
            b = x & -x; i = b.bit_length() - 1; lineok[i] &= Ll; x ^= b
        m = G
        while m:
            b = m & -m; i = b.bit_length() - 1; ptok[i] &= Pp; m ^= b
    adj = []
    for x in range(N):
        if x in F: adj.append([F[x]]); continue
        row = []; m = lineok[x]
        while m:
            b = m & -m; M = b.bit_length() - 1; m ^= b
            if ptok[M] >> x & 1: row.append(M)
        adj.append(row)
    matchR = [-1] * N; matchL = [-1] * N
    if sig0:     # warm start: keep sigma0 edges that are allowed
        for x in range(N):
            M = sig0[x]
            if M in adj[x] and matchR[M] < 0: matchR[M] = x; matchL[x] = M
    for x in F:
        M = F[x]
        if matchR[M] >= 0 and matchR[M] != x: matchL[matchR[M]] = -1
        matchR[M] = x; matchL[x] = M
    sys.setrecursionlimit(20000)
    def aug(u, seen):
        for v in adj[u]:
            if v in seen: continue
            seen.add(v)
            if matchR[v] < 0 or aug(matchR[v], seen):
                matchR[v] = u; matchL[u] = v; return True
        return False
    for u in range(N):
        if matchL[u] < 0: aug(u, set())
    return sum(1 for u in range(N) if matchL[u] >= 0), matchL

flags = []
fails = 0
cands = [(p, l) for p in range(N) for l in lof[p]]
import os
kmax = int(os.environ.get('KMAX', '999'))
while fails < tries and len(flags) < kmax:
    p, l = rng.choice(cands)
    if any(p == f or l == g for f, g in flags): fails += 1; continue
    sz, _ = matching(flags + [(p, l)])
    if sz == N: flags.append((p, l)); fails = 0; print('k', len(flags), flush=True)
    else: fails += 1
sz, mL = matching(flags)
coll = sum(1 for i in range(len(flags)) for j in range(i) if Pm[flags[i][0]] >> flags[j][0] & 1)
conc = sum(1 for i in range(len(flags)) for j in range(i) if Lm[flags[i][1]] >> flags[j][1] & 1)
print('FLAGS', len(flags), ' '.join(f'{p}:{l}' for p, l in flags))
print('collinear freed-point pairs', coll, 'concurrent freed-line pairs', conc, 'of', len(flags) * (len(flags) - 1) // 2)
if sig0: print('changed from sigma0', sum(1 for x in range(N) if mL[x] != sig0[x]))
print('SIGMA', ' '.join(map(str, mL)))
if len(sys.argv) > 5 and sig0:   # lift2/dmfast DM solution with the new sigma and SOLIN's flag voltages
    tok = open(sys.argv[4]).read().split(); nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
    with open(sys.argv[5], 'w') as f:
        f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, mL)); f.write(s + '\n' + s + '\n')
        f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
    with open(sys.argv[5] + '.free', 'w') as f: f.write(' '.join(str(p) for p, l in flags) + '\n')
