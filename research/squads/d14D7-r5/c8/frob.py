#!/usr/bin/env python3
"""c8 (wildcard B): Frobenius-normalised subgroups of the non-split tori of SO(7,11).

Block kind K in {E6, H6, E4, H4} (ovlib.block): torus T = <t> of order n in block coordinates, and the Frobenius
S of order k with S t S^-1 = t^q (x -> x^q in the field model; on the W + W* blocks S = diag(S_W, S_W^-T)).
N = T x| <S> acts on the block.  Every subgroup H of N that is not inside T equals <t^c, t^b S^j> with c = n/m
(C_m = H cap T), and b only matters modulo gcd(c, q^j - 1) (conjugation by T maps b to b + s(1 - q^j)).
So all such H are enumerated exactly.  Each H is embedded as block (+) identity on the complement (complement
types as in ovlib.torus), conjugated to the standard form by the P of ovlib.torus, and checked to be isometries.
Optionally eps = diag(I_block, -I_rest) is added (the complement sign).  Each group goes to orbclq.

usage: frob.py KIND [--lo 6] [--hi 400] [--t 10] [--eps] [--max 0] [--seed 1] [--list] [--only NAME,NAME]
Output: research/squads/d14D7-r5/c8/gens/*.txt, runs_KIND.jsonl (one line per run), sets/set_*.txt (kept if >= 600).
"""
import sys, os, json, time, subprocess, math, argparse

HERE = os.path.dirname(os.path.abspath(__file__))
OVO = '/home/user/degree-diameter/research/cell147/ovoid'
sys.path.insert(0, OVO)
import ovlib as L  # noqa: E402

q = 11
ORB = os.path.join(OVO, 'orbclq')
TYPES = {'E6': ['E6', 'L'], 'H6': ['H6', 'L'], 'E4': ['E4', 'H', 'L'], 'H4': ['H4', 'H', 'L']}
KF = {'E6': 6, 'H6': 3, 'E4': 4, 'H4': 2}      # order of the Frobenius on the block
DIM = {'E6': 6, 'H6': 6, 'E4': 4, 'H4': 4}


def frob_matrix(F):
    """matrix of x -> x^q in the power basis (columns = images of t^j)."""
    k = F.k
    cols = [F.pow([int(i == j) for i in range(k)], q) for j in range(k)]
    return [[cols[j][i] for j in range(k)] for i in range(k)]


def block_data(kind):
    """(t, n, S): block-coordinate torus generator t (order n) and Frobenius S with S t S^-1 = t^q, S^k = 1."""
    gram, t, n = L.block(kind, q)
    d = DIM[kind]
    if kind in ('E6', 'E4'):
        S = frob_matrix(L.GF(q, d))
    else:
        kk = d // 2
        Sw = frob_matrix(L.GF(q, kk))
        SiT = L.mat_T(L.mat_inv(Sw, q))
        S = [[0] * d for _ in range(d)]
        for i in range(kk):
            for j in range(kk):
                S[i][j] = Sw[i][j]
                S[kk + i][kk + j] = SiT[i][j]
    assert L.mat_pow(S, KF[kind], q) == L.mat_id(d), 'Frobenius order'
    assert L.mat_mul(L.mat_mul(S, t, q), L.mat_inv(S, q), q) == L.mat_pow(t, q, q), 'S t S^-1 != t^q'
    assert L.is_isometry(S, gram, q), 'Frobenius not an isometry of the block form'
    return t, n, S, gram


def divisors(n):
    return [m for m in range(1, n + 1) if n % m == 0]


def subgroups(n, k, lo, hi):
    """all subgroups H = <t^c, t^b S^j> (j != 0) of N = Z_n x| Z_k (elements (x, y) = t^x S^y) with lo <= |H| <= hi."""
    qp = [pow(q, y, n) for y in range(k)]

    def mul(a, b):
        return ((a[0] + qp[a[1]] * b[0]) % n, (a[1] + b[1]) % k)

    def closure(gens):
        I = (0, 0)
        seen = {I}
        frontier = [I]
        while frontier:
            nf = []
            for x in frontier:
                for g in gens:
                    y = mul(x, g)
                    if y not in seen:
                        seen.add(y)
                        nf.append(y)
                        if len(seen) > hi:
                            return None
            frontier = nf
        return frozenset(seen)

    found = {}
    for m in divisors(n):
        c = n // m
        for j in range(1, k):
            for b in range(math.gcd(c, q ** j - 1)):
                H = closure([(c % n, 0), (b, j)])
                if H is None or len(H) < lo:
                    continue
                if H not in found:
                    tor = sum(1 for x in H if x[1] == 0)
                    found[H] = dict(m=m, c=c, b=b, j=j, order=len(H), torus_part=tor)
    return sorted(found.values(), key=lambda r: (r['order'], r['m'], r['j'], r['b']))


def torus_setup(kind):
    types = TYPES[kind]
    gens, orders, P = L.torus(types, q)
    return P, L.mat_inv(P, q)


def embed(B, d):
    X = L.mat_id(7)
    for i in range(d):
        for j in range(d):
            X[i][j] = B[i][j] % q
    return X


def to_std(X, P, Pi):
    M = L.mat_mul(L.mat_mul(P, X, q), Pi, q)
    assert L.is_isometry(M, L.std_gram(q), q), 'not an isometry in standard coordinates'
    return M


def group_mats(kind, grp, t, n, S, d, P, Pi, eps):
    """generator matrices (7x7, standard coordinates) of the group described by grp."""
    k = KF[kind]
    mats = []
    if grp['c'] % n != 0:
        mats.append(to_std(embed(L.mat_pow(t, grp['c'], q), d), P, Pi))
    elem = L.mat_mul(L.mat_pow(t, grp['b'], q), L.mat_pow(S, grp['j'], q), q)
    mats.append(to_std(embed(elem, d), P, Pi))
    if eps:
        E = L.mat_id(7)
        for i in range(d, 7):
            E[i][i] = q - 1          # -1 on the complement, identity on the block (block coordinates)
        mats.append(to_std(E, P, Pi))
    return mats


def parse_result(stdout):
    res = {}
    for line in stdout.splitlines():
        if line.startswith('RESULT'):
            for kv in line.split()[1:]:
                if '=' not in kv:
                    continue
                key, val = kv.split('=', 1)
                try:
                    res[key] = float(val) if '.' in val else int(val)
                except ValueError:
                    res[key] = val
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('kind', choices=sorted(TYPES))
    ap.add_argument('--lo', type=int, default=6)
    ap.add_argument('--hi', type=int, default=400)
    ap.add_argument('--t', type=float, default=10)
    ap.add_argument('--eps', action='store_true', help='also add eps = diag(I_block, -I_rest)')
    ap.add_argument('--max', type=int, default=0)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--only', default='')
    a = ap.parse_args()
    kind = a.kind
    t, n, S, gram = block_data(kind)
    d = DIM[kind]
    groups = subgroups(n, KF[kind], a.lo, a.hi)
    print(f'{kind}: torus order {n}, Frobenius order {KF[kind]}, {len(groups)} subgroups with order in [{a.lo},{a.hi}]',
          flush=True)
    if a.list:
        for g in groups:
            print(g)
        return
    P, Pi = torus_setup(kind)
    gdir = os.path.join(HERE, 'gens')
    sdir = os.path.join(HERE, 'sets')
    os.makedirs(gdir, exist_ok=True)
    os.makedirs(sdir, exist_ok=True)
    runlog = os.path.join(HERE, f'runs_{kind}.jsonl')
    done = set()
    if os.path.exists(runlog):
        for line in open(runlog):
            try:
                done.add(json.loads(line)['name'])
            except Exception:
                pass
    only = set(x for x in a.only.split(',') if x)
    count = 0
    best_all = 0
    for grp in groups:
        name = f"{kind}_m{grp['m']}_b{grp['b']}_j{grp['j']}" + ('_eps' if a.eps else '')
        if only and name not in only:
            continue
        if name in done:
            continue
        if a.max and count >= a.max:
            break
        count += 1
        mats = group_mats(kind, grp, t, n, S, d, P, Pi, a.eps)
        gpath = os.path.join(gdir, name + '.txt')
        L.write_gens(gpath, mats, f'c8 {kind} torus C_{n}, Frobenius order {KF[kind]}: m={grp["m"]} (C_m = <t^{grp["c"]}>), '
                                  f't^{grp["b"]} S^{grp["j"]}, |H|={grp["order"]}' + (', with eps' if a.eps else ''))
        outp = os.path.join(sdir, 'set_' + name + '.txt')
        t0 = time.time()
        r = subprocess.run([ORB, gpath, '-q', str(q), '-t', str(a.t), '-s', str(a.seed), '-o', outp],
                           capture_output=True, text=True)
        res = parse_result(r.stdout)
        rec = dict(name=name, kind=kind, m=grp['m'], b=grp['b'], j=grp['j'], order=grp['order'],
                   torus_part=grp['torus_part'], eps=a.eps, **{k: v for k, v in res.items()},
                   wall=round(time.time() - t0, 1))
        if 'best' not in res:
            rec['stderr'] = r.stderr[-300:]
        with open(runlog, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        b = res.get('best', 0)
        best_all = max(best_all, b)
        if b < 600 and os.path.exists(outp):
            os.remove(outp)
        print(f"[{count}] {name} |H|={grp['order']} torusPart={grp['torus_part']} K={res.get('good')} "
              f"best={b} wall={rec['wall']} (run best {best_all})", flush=True)


if __name__ == '__main__':
    main()
