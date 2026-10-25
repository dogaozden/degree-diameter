"""Haar screen over ALL groups of a squarefree order N (for orders the SmallGroups library lacks).

Hoelder: every group of squarefree order is Z_m x|_r Z_n with m n = N, r^n = 1 (mod m) and gcd(r - 1, m) = 1 (m = |G'|).
We list every such (m, n, r), with r up to r -> r^u (u a unit mod n), which covers every isomorphism class (duplicates
are possible and harmless), then anneal each with hanneal (lozlike.table builds the multiplication table).
Filter (rigorous, as fscreen.py): abfilt's abelianization bound with G' = Z_m and G^ab = Z_n (cyclic, so the rank
filter never applies). Groups it excludes are logged as abfail.
Usage: SCRATCH=dir python3 sqfmeta.py DELTA D N [N ...] [--secs 10] [--seeds 1] [--list | --dry | --check]
--check compares the number of listed groups with Hoelder's formula and NrSmallGroups (runs/sqfmeta_count_check.txt:
28 orders agree with the formula, 19 of them also with GAP; the other 9 are not in the installed library).
Output: <OUTDIR or runs>/sqfmeta_d{DELTA}D{D}.tsv: N m n r costs best_set
"""
import argparse
import os
import subprocess
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from allgroups import abfilt  # noqa: E402
from lozlike import table  # noqa: E402

SP = os.environ.get('SCRATCH', '/tmp')


def primes_of(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def holder_count(N):
    """Hoelder's formula: sum over m | N of prod over p | m of (p^c(p) - 1) / (p - 1), c(p) = #{q | N/m prime, q = 1 mod p}."""
    from itertools import combinations
    ps, tot = primes_of(N), 0
    for t in range(len(ps) + 1):
        for mp in combinations(ps, t):
            n = N
            for p in mp:
                n //= p
            term = 1
            for p in mp:
                c = sum(1 for q in primes_of(n) if q % p == 1)
                term *= (p ** c - 1) // (p - 1)
            tot += term
    return tot


def groups(N):
    ps = primes_of(N)
    assert all(N % (q * q) for q in ps), f'{N} is not squarefree'
    out = []
    from itertools import combinations
    for t in range(0, len(ps) + 1):
        for mp in combinations(ps, t):
            m = 1
            for q in mp:
                m *= q
            n = N // m
            if m == 1:
                out.append((1, n, 0))          # cyclic group Z_N
                continue
            seen = set()
            units = [u for u in range(1, n) if gcd(u, n) == 1] or [1]
            for r in range(2, m):
                if gcd(r, m) != 1 or gcd(r - 1, m) != 1 or pow(r, n, m) != 1 or r in seen:
                    continue
                seen |= {pow(r, u, m) for u in units}
                out.append((m, n, r))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('orders', type=int, nargs='+')
    ap.add_argument('--secs', type=float, default=10)
    ap.add_argument('--seeds', type=int, default=1)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--dry', action='store_true', help='apply the filter only; do not anneal')
    ap.add_argument('--check', action='store_true', help='compare the number of groups listed with NrSmallGroups')
    a = ap.parse_args()
    outp = os.path.join(os.environ.get('OUTDIR', os.path.join(HERE, 'runs')), f'sqfmeta_d{a.Delta}D{a.D}.tsv')
    done = set()
    if os.path.exists(outp):
        done = {tuple(map(int, l.split('\t')[:4])) for l in open(outp) if l[0].isdigit()}
    if a.check:
        from allgroups import gap
        out = gap('ns := [' + ','.join(map(str, a.orders)) + '];; Print(List(ns, function(n) if SmallGroupsAvailable(n) '
                  'then return NrSmallGroups(n); else return -1; fi; end), "\\n"); QUIT;\n', 600)
        nr = [int(x) for x in out.replace('[', ' ').replace(']', ' ').replace(',', ' ').split()]
        for N, g in zip(a.orders, nr):
            mine = len(groups(N))
            h = holder_count(N)
            print(N, 'listed', mine, 'Hoelder', h, 'GAP', g if g >= 0 else 'not in library',
                  'ok' if mine == h and g in (h, -1) else 'MISMATCH')
        return
    log = open(os.devnull if (a.list or a.dry) else outp, 'a')
    for N in a.orders:
        gs = groups(N)
        if a.list:
            print(N, len(gs), gs)
            continue
        for (m, n, r) in gs:
            if (N, m, n, r) in done:
                continue
            fr = abfilt(a.Delta, a.D, m, [n])
            if fr.startswith('pass 0 '):
                log.write(f'{N}\t{m}\t{n}\t{r}\tabfail\t-\n'); log.flush()
                continue
            if a.dry:
                print(N, m, n, r, fr)
                continue
            tab = os.path.join(SP, f'sq_{m}_{n}_{r}_{os.getpid()}.txt')
            table(m, n, r, tab)
            costs, bset = [], '-'
            for s in range(1, a.seeds + 1):
                out = subprocess.run([os.path.join(HERE, 'hanneal'), tab, str(a.Delta), str(a.D), str(a.secs), str(s), '8',
                                      os.path.join(SP, f'sq_sol_{m}_{n}_{r}_{s}.txt')], capture_output=True, text=True).stdout
                res = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
                best = int(res[4].split('=')[1])
                if not costs or best < min(costs):
                    bset = ' '.join(res[res.index('best_set') + 1:])
                costs.append(best)
                if best == 0:
                    print(f'*** N={N} Z{m} x|_{r} Z{n}: cost 0, S = {bset}', flush=True)
                    break
            log.write(f'{N}\t{m}\t{n}\t{r}\t{",".join(map(str, costs))}\t{bset}\n')
            log.flush()
            os.remove(tab)


if __name__ == '__main__':
    main()
