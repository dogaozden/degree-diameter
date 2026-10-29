#!/usr/bin/env python3
"""Slot counts of typed level layouts with 2k+1 levels (D7_THEOREMS.md, Section 3).

A layout is a regular tournament T on 2k+1 levels (every pair of levels joined by one transition, k out and k in at
every level) and a type H or D for every level.  A friendly transition (types differ) frees P points (source H) or
Lam lines (source D); a non-friendly one frees m elements.  alpha_j = free slots on the transitions out of level j,
beta_j = free slots on the transitions into level j; the hubs per side are at most min alpha and min beta.

Parts:
  1. rotational tournament (j -> j+i, 1 <= i <= k), all 2^(2k+1) typings, k = 1..8: the best typings, and the
     alternating typing (HD)^k H, with the slot minima written as (number of friendly transitions, P or Lam);
  2. every labelled regular tournament on 5 and 7 levels with every typing (exhaustive);
  3. SAT (python-sat) on 9 and 11 levels: is there a regular tournament and typing with both minima equal to the
     upper bound a P + (k-a) m (a = floor(k/2))?  (Theorem 3.3 says no for k even; this tests k odd.)
Output: slots.out"""
import itertools, sys
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

def mins(L, arcs, types, P, Lam, m):
    al = [0] * L; be = [0] * L
    for (i, j) in arcs:
        f = (P if types[i] == 'H' else Lam) if types[i] != types[j] else m
        al[i] += f; be[j] += f
    return min(al), min(be), al, be

def sym(L, arcs, types):
    """symbolic minima: for every level the pair (friendly count, 'P'/'L'); return the lexicographically smallest for
    alpha and beta (valid when Lam - m > a (P - Lam), true for all prime powers q > a, Lemma 3.2)"""
    fo = [0] * L; fi = [0] * L
    for (i, j) in arcs:
        if types[i] != types[j]:
            fo[i] += 1; fi[j] += 1
    a_key = min((fo[j], 1 if types[j] == 'H' else 0) for j in range(L))   # alpha: H level -> P (bigger)
    b_key = min((fi[j], 0 if types[j] == 'H' else 1) for j in range(L))   # beta: D level -> P
    fmt = lambda key: '%d%s' % (key[0], 'P' if key[1] else 'L')
    return fmt(a_key), fmt(b_key), a_key, b_key

out = open('slots.out', 'w')
def say(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

# numeric test values: (q, P, Lam, m) with P = (q+1)(q^3+1), Lam = q^4+q^2+q, m = q^2+1 or the lab's mirrored sets
def vals(q, m=None):
    return (q, (q + 1) * (q ** 3 + 1), q ** 4 + q ** 2 + q, q * q + 1 if m is None else m)
TEST = [vals(11, 768), vals(13, 792), vals(16), vals(101), vals(1009)]

say('== 1. rotational tournament, all typings')
for k in range(1, 9):
    L = 2 * k + 1
    arcs = [(j, (j + i) % L) for j in range(L) for i in range(1, k + 1)]
    alt = ''.join('HD'[j % 2] for j in range(L))
    best = {}
    for T in itertools.product('HD', repeat=L):
        if T[0] != 'H':
            continue
        sa, sb, ka, kb = sym(L, arcs, T)
        best.setdefault((ka[0] + kb[0], ka[1] + kb[1]), []).append((sa, sb, ''.join(T)))
    top = max(best)
    ex = best[top]
    sa, sb, _, _ = sym(L, arcs, alt)
    say('k=%d L=%d: best symbolic (min alpha, min beta) =' % (k, L), sorted(set((e[0], e[1]) for e in ex)),
        ' #typings', len(ex), ' e.g.', ex[0][2], '| alternating', alt, '->', sa, sb)
    for (q, P, Lam, m) in TEST:
        bestnum = max(sum(mins(L, arcs, T, P, Lam, m)[:2]) for T in itertools.product('HD', repeat=L) if T[0] == 'H')
        a1, b1, _, _ = mins(L, arcs, alt, P, Lam, m)
        if bestnum != a1 + b1:
            say('   NUMERIC MISMATCH q=%d: best %d alternating %d' % (q, bestnum, a1 + b1))
    say('   numeric check (q = 11 m=768, 13 m=792, 16, 101, 1009): alternating attains the numeric optimum')

say('== 2. all labelled regular tournaments on 5 and 7 levels, all typings')
def regular_tournaments(L):
    k = (L - 1) // 2
    pairs = [(i, j) for i in range(L) for j in range(i + 1, L)]
    outd = [0] * L; ind = [0] * L; arcs = []
    def rec(t):
        if t == len(pairs):
            yield list(arcs); return
        i, j = pairs[t]
        for (a, b) in ((i, j), (j, i)):
            if outd[a] < k and ind[b] < k:
                outd[a] += 1; ind[b] += 1; arcs.append((a, b))
                yield from rec(t + 1)
                arcs.pop(); outd[a] -= 1; ind[b] -= 1
    yield from rec(0)
for L in (5, 7):
    k = (L - 1) // 2
    nt = 0; best = {}
    for arcs in regular_tournaments(L):
        nt += 1
        for T in itertools.product('HD', repeat=L):
            sa, sb, ka, kb = sym(L, arcs, T)
            key = (ka[0] + kb[0], ka[1] + kb[1])
            best[key] = best.get(key, 0) + 1
    top = max(best)
    say('L=%d: %d labelled regular tournaments; best (sum of friendly counts, number of P-minima) = %s in %d (tournament, typing) pairs'
        % (L, nt, top, best[top]))

say('== 3. SAT: both minima equal to a P + (k-a) m ?')
def sat_both_P(L):
    k = (L - 1) // 2; a = k // 2
    pool = IDPool(); cnf = CNF()
    arc = {}
    for i in range(L):
        for j in range(i + 1, L):
            v = pool.id(('x', i, j)); arc[(i, j)] = v; arc[(j, i)] = -v
    t = [pool.id(('t', j)) for j in range(L)]   # true = H
    def card_ge(lits, b, cond=None):
        if b <= 0:
            return
        enc = CardEnc.atleast(lits=lits, bound=b, vpool=pool, encoding=EncType.seqcounter)
        for cl in enc.clauses:
            cnf.append(cl + ([-cond] if cond else []))
    for j in range(L):
        outs = [arc[(j, i)] for i in range(L) if i != j]
        for cl in CardEnc.equals(lits=outs, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses:
            cnf.append(cl)
    # y[j][i] <-> arc j->i and types differ
    fo = {j: [] for j in range(L)}; fi = {j: [] for j in range(L)}
    for j in range(L):
        for i in range(L):
            if i == j:
                continue
            y = pool.id(('y', j, i)); x = arc[(j, i)]
            d = pool.id(('d', min(i, j), max(i, j)))
            # d <-> t_i xor t_j
            cnf.extend([[-d, t[i], t[j]], [-d, -t[i], -t[j]], [d, -t[i], t[j]], [d, t[i], -t[j]]])
            cnf.extend([[-y, x], [-y, d], [y, -x, -d]])
            fo[j].append(y); fi[i].append(y)
    for j in range(L):
        card_ge(fo[j], a); card_ge(fi[j], a)
        card_ge(fo[j], a + 1, cond=-t[j])   # D level: a+1 friendly out  (alpha minimum at an H level only)
        card_ge(fi[j], a + 1, cond=t[j])    # H level: a+1 friendly in   (beta minimum at a D level only)
    with Cadical153(bootstrap_with=cnf.clauses) as s:
        return s.solve()
for L in (5, 7, 9, 11, 13):
    k = (L - 1) // 2
    say('L=%d k=%d: regular tournament + typing with min alpha = min beta = %dP + %dm: %s'
        % (L, k, k // 2, k - k // 2, 'SAT' if sat_both_P(L) else 'UNSAT'))
