"""Direct products G x H of two groups as Cayley tables for ctrl_search.c (format: "g", then g*g entries T[a*g+b] = a*b).
usage: python3 prodgroups.py A B OUT [SAMPLES]
  A, B: a groups.py name (cyc:6, a4, s4, sl:3, dih:4, q8, dic:3, prod:2:2, ...), 'heis27' (Heisenberg group of order 27,
        built here), or a path to an existing table file in the same format.
  Element (a, b) of the product has index a*|B| + b.  OUT is written in the same format.
  Checks: each factor is a group (groups.check); the product rows are permutations (Latin square); identity found;
  associativity of the product on SAMPLES random triples (default 200000).
"""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'theorems', 'chartlift'))
import groups

def heis27():
    E = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
    return groups.table_from(E, lambda x, y: ((x[0] + y[0]) % 3, (x[1] + y[1]) % 3, (x[2] + y[2] + x[0] * y[1]) % 3))

def read_table(path):
    toks = open(path).read().split()
    g = int(toks[0]); T = [int(x) for x in toks[1:1 + g * g]]
    assert len(T) == g * g, 'short table ' + path
    return [T[i * g:(i + 1) * g] for i in range(g)]

def load(spec):
    if os.path.isfile(spec): return read_table(spec)
    if spec == 'heis27': return heis27()
    return groups.make(spec)

def product(A, B):
    ga, gb = len(A), len(B); n = ga * gb
    T = [[0] * n for _ in range(n)]
    for a1 in range(ga):
        for b1 in range(gb):
            row = T[a1 * gb + b1]
            for a2 in range(ga):
                base = A[a1][a2] * gb
                Brow = B[b1]
                for b2 in range(gb):
                    row[a2 * gb + b2] = base + Brow[b2]
    return T

def check_group(T, samples, rng):
    n = len(T)
    for row in T: assert sorted(row) == list(range(n)), 'row is not a permutation'
    ident = [e for e in range(n) if all(T[e][j] == j for j in range(n))]
    assert len(ident) == 1 and all(T[j][ident[0]] == j for j in range(n)), 'no two-sided identity'
    for _ in range(samples):
        a, b, c = rng.randrange(n), rng.randrange(n), rng.randrange(n)
        if T[T[a][b]][c] != T[a][T[b][c]]: raise AssertionError('associativity fails at %s' % ((a, b, c),))
    return n, ident[0]

if __name__ == '__main__':
    sa, sb, out = sys.argv[1], sys.argv[2], sys.argv[3]
    samples = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
    A, B = load(sa), load(sb)
    for spec, T in ((sa, A), (sb, B)):
        if len(T) <= 60: groups.check(T)              # full associativity for small factors
    T = product(A, B)
    n, e = check_group(T, samples, random.Random(1))
    with open(out, 'w') as f:
        f.write('%d\n' % n); f.write(' '.join(str(x) for row in T for x in row) + '\n')
    print('%s x %s order %d identity %d sampled-assoc %d ok -> %s' % (sa, sb, n, e, samples, out))
