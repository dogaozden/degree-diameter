"""flaggreedy2.py GQBIN SEED TRIES SOLIN OUTSOL: relaxed version of flaggreedy.py (card c2, round 1).

Grows freed flags (p in l = sigma(p)) while the exact-coverage matching keeps size >= N - DEF (env DEF, default 0),
up to KMAX flags (env KMAX).  The final maximum matching is completed to a full bijection sigma: unmatched points get
unmatched lines, preferring the point's sigma0 line (SOLIN's sigma) when it is free, else a random free line.
Writes OUTSOL (lift2 DM format, flag voltages nu copied from SOLIN) and OUTSOL.free (freed points), as flaggreedy does.
Prints the flags, the matching deficiency, and the number of points whose sigma changed from sigma0."""
import sys, random, os
sys.path.insert(0, '.')
from gq import load, perp, lperp

q, N, lines, lof = load(sys.argv[1]); seed = int(sys.argv[2]); tries = int(sys.argv[3])
rng = random.Random(seed)
tok = open(sys.argv[4]).read().split(); sig0 = list(map(int, tok[7:7 + N]))
outsol = sys.argv[5]
DEF = int(os.environ.get('DEF', '0')); KMAX = int(os.environ.get('KMAX', '6'))
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
    for x in range(N):           # warm start: keep sigma0 edges that are allowed
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
while fails < tries and len(flags) < KMAX:
    p, l = rng.choice(cands)
    if any(p == f or l == g for f, g in flags): fails += 1; continue
    sz, _ = matching(flags + [(p, l)])
    if sz >= N - DEF: flags.append((p, l)); fails = 0; print('k', len(flags), 'matching', sz, 'deficiency', N - sz, flush=True)
    else: fails += 1
sz, mL = matching(flags)
print('final matching', sz, 'deficiency', N - sz, 'DEF', DEF)
# complete the maximum matching to a bijection
used = set(M for M in mL if M >= 0)
free_lines = [M for M in range(N) if M not in used]
rng.shuffle(free_lines)
nfill = 0
for x in range(N):
    if mL[x] >= 0: continue
    if sig0[x] in free_lines:
        M = sig0[x]
    else:
        M = free_lines[0]
    free_lines.remove(M); mL[x] = M; nfill += 1
assert sorted(mL) == list(range(N))
for p, l in flags: assert mL[p] == l, (p, l, mL[p])
coll = sum(1 for i in range(len(flags)) for j in range(i) if Pm[flags[i][0]] >> flags[j][0] & 1)
conc = sum(1 for i in range(len(flags)) for j in range(i) if Lm[flags[i][1]] >> flags[j][1] & 1)
print('FLAGS', len(flags), ' '.join(f'{p}:{l}' for p, l in flags))
print('deficiency', N - sz, 'filled points', nfill)
print('collinear freed-point pairs', coll, 'concurrent freed-line pairs', conc, 'of', len(flags) * (len(flags) - 1) // 2)
print('changed from sigma0', sum(1 for x in range(N) if mL[x] != sig0[x]))
print('SIGMA', ' '.join(map(str, mL)))
nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
with open(outsol, 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, mL)); f.write(s + '\n' + s + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(outsol + '.free', 'w') as f: f.write(' '.join(str(p) for p, l in flags) + '\n')
print('WROTE', outsol, 'and', outsol + '.free')
