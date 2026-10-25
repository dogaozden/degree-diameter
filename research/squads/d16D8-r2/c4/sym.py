#!/usr/bin/env python3
"""c4: cyclic semiregular collineation group C of W(q); C-invariant Z_m lifts of I + 2 equivariant matchings.

  python3 sym.py group Q                     find S in Sp(4,Q) whose projective order is (Q^2+1)/2 and that acts
                                             semiregularly on points and lines (C = <S>); saves group_qQ.json
  python3 sym.py anneal Q M SECS SEED TAG    anneal orbit parameters for a Z_M design; saves tmp/ and best_* files

Design (C-invariant): flag voltages constant on C-orbits of flags (param fv[orbit]); for each matching k, a bijection
pi_k from point-orbits to line-orbits and offsets t_k[i] in Z_d, so that M_k(g^a p_i) = g^(a+t) l_{pi(i)}; matching
voltages w_k[i] constant on the orbit of edges (g^a p_i, M_k(g^a p_i)). The cost is the number of uncovered pairs
summed over one source per C-orbit of base vertices (exact for C-invariant designs: each orbit contributes d times).
"""
import sys, os, json, random, math, time, re, subprocess, copy
sys.path.insert(0, '/home/user/degree-diameter/research/d16D8')
import gq

HERE = '/home/user/degree-diameter/research/squads/d16D8-r2/c4'
BASELIFT = '/home/user/degree-diameter/research/d16D8/baselift'
J = [[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]]   # B(x,y) = x^T J y


def mm(A, B, q):
    return [[sum(A[i][k] * B[k][j] for k in range(4)) % q for j in range(4)] for i in range(4)]


def tr(A):
    return [list(r) for r in zip(*A)]


def norm(v, q):
    v = [x % q for x in v]
    for x in v:
        if x:
            inv = pow(x, q - 2, q)
            return tuple(y * inv % q for y in v)
    return None


def app(S, v, q):
    return [sum(S[i][k] * v[k] for k in range(4)) % q for i in range(4)]


def is_sp_up_to_scalar(S, q):
    M = mm(mm(tr(S), J, q), S, q)
    mu = M[0][1] % q
    return all((M[i][j] - mu * J[i][j]) % q == 0 for i in range(4) for j in range(4))


def transvection(v, a, q):
    Jv = [sum(J[i][k] * v[k] for k in range(4)) % q for i in range(4)]
    return [[((1 if i == j else 0) + a * v[i] * Jv[j]) % q for j in range(4)] for i in range(4)]


def is_scalar(P, q):
    return (all(P[i][j] == 0 for i in range(4) for j in range(4) if i != j)
            and len({P[i][i] for i in range(4)}) == 1 and P[0][0] % q != 0)


def proj_order(S, q, cap):
    P, j = S, 1
    while not is_scalar(P, q):
        P = mm(P, S, q); j += 1
        if j > cap:
            return None
    return j


def random_sp(q, rnd, r=10):
    S = [[int(i == j) for j in range(4)] for i in range(4)]
    for _ in range(r):
        v = [rnd.randrange(q) for _ in range(4)]
        if not any(v):
            continue
        S = mm(S, transvection(v, rnd.randrange(1, q), q), q)
    return S


def perms_of_powers(q, S, d, G):
    N = G['N']; pts = G['pts']; lines = G['lines']
    pidx = {p: i for i, p in enumerate(pts)}
    lidx = {tuple(L): j for j, L in enumerate(lines)}
    P = [[int(i == j) for j in range(4)] for i in range(4)]
    pp, pl = [], []
    for j in range(d):
        perm = [pidx[norm(app(P, pts[p], q), q)] for p in range(N)]
        lperm = [lidx[tuple(sorted(perm[p] for p in lines[l]))] for l in range(N)]   # KeyError if a line is not mapped to a line
        pp.append(perm); pl.append(lperm)
        P = mm(P, S, q)
    return pp, pl


def find_group(q, seed=1, tries=200000):
    G = gq.load(q); N = G['N']
    target = (q * q + 1) // 2
    rnd = random.Random(seed)
    seen = {}
    for t in range(tries):
        S = random_sp(q, rnd)
        if not is_sp_up_to_scalar(S, q):
            raise SystemExit('not symplectic?!')
        d = proj_order(S, q, 10 * (q * q + 1))
        if d is None:
            continue
        seen[d] = seen.get(d, 0) + 1
        if d != target:
            continue
        pp, pl = perms_of_powers(q, S, d, G)
        ok = all(all(pp[j][p] != p for p in range(N)) and all(pl[j][l] != l for l in range(N)) for j in range(1, d))
        if ok:
            print('tries', t + 1, 'orders seen', sorted(seen.items())[:12], file=sys.stderr)
            return S, d
    raise SystemExit('no semiregular element of order %d found; orders seen %s' % (target, sorted(seen.items())))


def cmd_group(q):
    S, d = find_group(q)
    G = gq.load(q); N = G['N']
    pp, pl = perms_of_powers(q, S, d, G)
    print('q=%d S=%s projective order d=%d' % (q, S, d))
    print('all powers map lines to lines: True (checked for every power)')
    print('semiregular on points and lines: True; point orbits %d, line orbits %d, flags %d'
          % (N // d, N // d, sum(len(L) for L in G['lines'])))
    json.dump({'q': q, 'S': S, 'd': d}, open(os.path.join(HERE, 'group_q%d.json' % q), 'w'))


def structure(q, S, d):
    G = gq.load(q); N = G['N']; lines = G['lines']
    pp, pl = perms_of_powers(q, S, d, G)
    porb = [-1] * N; pexp = [0] * N; preps = []
    for p in range(N):
        if porb[p] < 0:
            o = len(preps); preps.append(p)
            for j in range(d):
                x = pp[j][p]; assert porb[x] < 0; porb[x] = o; pexp[x] = j
    lorb = [-1] * N; lexp = [0] * N; lreps = []
    for l in range(N):
        if lorb[l] < 0:
            o = len(lreps); lreps.append(l)
            for j in range(d):
                x = pl[j][l]; assert lorb[x] < 0; lorb[x] = o; lexp[x] = j
    assert len(preps) == len(lreps)
    fo = {}; nf = 0
    for l in range(N):
        for p in lines[l]:
            if (p, l) in fo:
                continue
            for j in range(d):
                key = (pp[j][p], pl[j][l]); assert key not in fo; fo[key] = nf
            nf += 1
    flags = [(p, l, fo[(p, l)]) for l in range(N) for p in lines[l]]
    return dict(N=N, d=d, pl=pl, porb=porb, pexp=pexp, preps=preps, lreps=lreps, nf=nf, flags=flags)


def random_state(T, m, rnd):
    d = T['d']; no = len(T['preps'])
    st = {'fv': [rnd.randrange(m) for _ in range(T['nf'])], 'pi': [], 't': [], 'w': []}
    for k in range(2):
        perm = list(range(no)); rnd.shuffle(perm)
        st['pi'].append(perm)
        st['t'].append([rnd.randrange(d) for _ in range(no)])
        st['w'].append([rnd.randrange(m) for _ in range(no)])
    return st


def write_base(T, st, m, fn):
    N, d, pl, porb, pexp, lreps = T['N'], T['d'], T['pl'], T['porb'], T['pexp'], T['lreps']
    out = []
    for (p, l, o) in T['flags']:
        out.append('%d %d %d 1' % (p, N + l, st['fv'][o]))
    for k in range(2):
        pik, tk, wk = st['pi'][k], st['t'][k], st['w'][k]
        for p in range(N):
            i = porb[p]
            L = pl[(pexp[p] + tk[i]) % d][lreps[pik[i]]]
            out.append('%d %d %d %d' % (p, N + L, wk[i], 100 + k))
    with open(fn, 'w') as f:
        f.write('%d %d %d\n' % (2 * N, m, len(out)))
        f.write('\n'.join(out)); f.write('\n')


def evaluate(fn, srcfn):
    env = dict(os.environ, THREADS='1', SRCFILE=srcfn)
    r = subprocess.run([BASELIFT, 'eval', fn, '6'], capture_output=True, text=True, env=env, timeout=900)
    mt = re.search(r'uncovered=(\d+)', r.stdout)
    if not mt:
        raise SystemExit('bad eval output: ' + r.stdout + r.stderr)
    return int(mt.group(1))


def full_eval(fn):
    env = dict(os.environ, THREADS='1'); env.pop('SRCFILE', None)
    r = subprocess.run([BASELIFT, 'eval', fn, '6'], capture_output=True, text=True, env=env, timeout=900)
    return r.stdout.strip()


def cmd_anneal(q, m, secs, seed, tag, T0=2.0, T1=0.1):
    gj = json.load(open(os.path.join(HERE, 'group_q%d.json' % q)))
    S, d = gj['S'], gj['d']
    T = structure(q, S, d)
    no = len(T['preps'])
    os.makedirs(os.path.join(HERE, 'tmp'), exist_ok=True)
    fn = os.path.join(HERE, 'tmp', '%s_q%d_m%d.base' % (tag, q, m))
    srcfn = os.path.join(HERE, 'tmp', 'srcs_q%d.txt' % q)
    with open(srcfn, 'w') as f:
        f.write(' '.join(str(x) for x in T['preps'] + [T['N'] + l for l in T['lreps']]) + '\n')
    rnd = random.Random(seed)
    st = random_state(T, m, rnd)
    write_base(T, st, m, fn); cur = evaluate(fn, srcfn); best = cur; best_st = copy.deepcopy(st)
    print('q=%d m=%d d=%d orbits=%d flag-orbits=%d start rep-uncovered=%d' % (q, m, d, no, T['nf'], cur), file=sys.stderr)
    t0 = time.time(); last = t0; it = 0; acc = 0
    while best > 0 and time.time() - t0 < secs:
        fr = (time.time() - t0) / secs
        Tm = T0 * (T1 / T0) ** fr
        r = rnd.random()
        if r < 0.6:
            o = rnd.randrange(T['nf']); old = st['fv'][o]; st['fv'][o] = (old + rnd.randrange(1, m)) % m
            undo = lambda o=o, old=old: st['fv'].__setitem__(o, old)
        elif r < 0.75:
            k = rnd.randrange(2); i = rnd.randrange(no); old = st['w'][k][i]
            st['w'][k][i] = (old + rnd.randrange(1, m)) % m
            undo = lambda k=k, i=i, old=old: st['w'][k].__setitem__(i, old)
        elif r < 0.9:
            k = rnd.randrange(2); i = rnd.randrange(no); old = st['t'][k][i]
            st['t'][k][i] = (old + rnd.randrange(1, d)) % d
            undo = lambda k=k, i=i, old=old: st['t'][k].__setitem__(i, old)
        else:
            k = rnd.randrange(2); i, i2 = rnd.sample(range(no), 2)
            def swap(k=k, i=i, i2=i2):
                pk = st['pi'][k]; pk[i], pk[i2] = pk[i2], pk[i]
            swap(); undo = swap
        write_base(T, st, m, fn)
        new = evaluate(fn, srcfn); it += 1
        if new <= cur or rnd.random() < math.exp(-(new - cur) / Tm):
            cur = new; acc += 1
            if cur < best:
                best = cur; best_st = copy.deepcopy(st)
        else:
            undo()
        if time.time() - last > 10:
            last = time.time()
            print('t=%.0f it=%d acc=%d T=%.3f cur=%d best=%d' % (time.time() - t0, it, acc, Tm, cur, best), file=sys.stderr)
    best_fn = os.path.join(HERE, 'tmp', 'best_%s_q%d_m%d.base' % (tag, q, m))
    write_base(T, best_st, m, best_fn)
    json.dump(best_st, open(os.path.join(HERE, 'tmp', 'best_%s_q%d_m%d.json' % (tag, q, m)), 'w'))
    res = 'rep-uncovered best=%d it=%d time=%.0fs' % (best, it, time.time() - t0)
    if best == 0:
        out = full_eval(best_fn)
        res += ' | FULL: ' + out
    print('RESULT q=%d m=%d d=%d %s file=%s' % (q, m, d, res, best_fn))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'group':
        cmd_group(int(sys.argv[2]))
    elif cmd == 'anneal':
        q, m, secs, seed = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
        tag = sys.argv[6] if len(sys.argv) > 6 else 'run'
        T0 = float(os.environ.get('T0', '2.0')); T1 = float(os.environ.get('T1', '0.1'))
        cmd_anneal(q, m, secs, seed, tag, T0, T1)
