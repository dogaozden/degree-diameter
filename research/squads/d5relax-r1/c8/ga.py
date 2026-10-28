#!/usr/bin/env python3
"""Card c8 (wildcard): memetic search for relaxed sets of W(q).

A population of relaxed sets evolves by crossover.  Crossover A x B either keeps the common points A & B and adds
the rest of A | B greedily (zero-conflict additions), or takes A outside a random closed neighbourhood and B inside
it.  The child is repaired (conflicting points dropped, then greedy additions over all points) and then improved by
the fixed-size tabu search rtabu for a few seconds, started from the child.  The child replaces the worst member if
it is at least as large and not a duplicate.

usage: python3 ga.py q SECONDS SEED OUT [CHILD_SECS] [POP] [INIT_FILE]
OUT: rtabu format (size, then points), rewritten at every improvement of the best size."""
import sys, os, random, subprocess, time, tempfile

D = '/home/user/degree-diameter/research/theorems/d5relax'
RT = os.path.join(D, 'rtabu')


def load_adj(q):
    tok = open(os.path.join(D, 'data', 'W%d_adj.txt' % q)).read().split()
    n = int(tok[0]); pos = 1; nbs = []
    for _ in range(n):
        d = int(tok[pos]); nbs.append([int(t) for t in tok[pos + 1:pos + 1 + d]]); pos += 1 + d
    return n, nbs


def relaxed(S, nbs):
    S = set(S)
    return all(sum(1 for w in nbs[v] if w in S) <= 1 for v in S)


def repair(S, nbs, rng):
    S = set(S)
    while True:
        cnt = {v: sum(1 for w in nbs[v] if w in S) for v in S}
        m = max(cnt.values(), default=0)
        if m < 2:
            return S
        cand = [v for v in cnt if cnt[v] == m]
        S.discard(rng.choice(cand))


def greedy_add(S, nbs, n, rng, pool):
    """add points of pool (in random order) that keep the set relaxed"""
    S = set(S)
    cnt = [0] * n
    for v in S:
        for w in nbs[v]:
            cnt[w] += 1
    order = list(pool); rng.shuffle(order)
    for v in order:
        if v in S or cnt[v] >= 2:
            continue
        if any((w in S) and cnt[w] >= 1 for w in nbs[v]):
            continue
        S.add(v)
        for w in nbs[v]:
            cnt[w] += 1
    return S


def crossover(A, B, nbs, n, rng):
    if rng.random() < 0.5:
        C = A & B
        S = greedy_add(C, nbs, n, rng, (A | B) - C)
    else:
        z = rng.randrange(n)
        R = set([z] + nbs[z])
        S = repair((A - R) | (B & R), nbs, rng)
    return greedy_add(S, nbs, n, rng, range(n))


def write_set(fn, S):
    with open(fn, 'w') as f:
        f.write('%d\n' % len(S))
        for v in sorted(S):
            f.write('%d\n' % v)


def read_set(fn):
    tok = open(fn).read().split()
    if not tok:
        return set()
    m = int(tok[0])
    return set(int(t) for t in tok[1:1 + m])


def run_rtabu(start, secs, seed, tmpdir, q):
    out = os.path.join(tmpdir, 'rt_out.txt')
    cmd = [RT, os.path.join(D, 'data', 'W%d_adj.txt' % q), '%g' % secs, str(seed), out]
    if start is not None:
        inp = os.path.join(tmpdir, 'rt_in.txt')
        write_set(inp, start)
        cmd += ['-i', inp]
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=secs + 60)
    return read_set(out)


def main():
    q = int(sys.argv[1]); total = float(sys.argv[2]); seed = int(sys.argv[3]); outf = sys.argv[4]
    child_secs = float(sys.argv[5]) if len(sys.argv) > 5 else 2.0
    P = int(sys.argv[6]) if len(sys.argv) > 6 else 8
    init = sys.argv[7] if len(sys.argv) > 7 else None
    rng = random.Random(seed)
    n, nbs = load_adj(q)
    tmpdir = os.path.join(os.path.dirname(os.path.abspath(outf)), 'tmp_s%d' % seed)
    os.makedirs(tmpdir, exist_ok=True)
    logf = open(outf + '.log', 'w')

    def say(msg):
        logf.write(msg + '\n'); logf.flush()

    t0 = time.time()
    pop = []
    if init:
        S0 = read_set(init)
        assert relaxed(S0, nbs), 'init set not relaxed'
        pop.append(S0)
    while len(pop) < P and time.time() - t0 < total:
        S = run_rtabu(None, child_secs, rng.randrange(1 << 30), tmpdir, q)
        if relaxed(S, nbs) and S not in pop:
            pop.append(S)
    best = max(pop, key=len)
    write_set(outf, best)
    say('init: sizes %s, %.0f s' % (sorted(len(s) for s in pop), time.time() - t0))
    gen = 0
    while time.time() - t0 < total:
        gen += 1
        i, j = rng.sample(range(len(pop)), 2)
        A, B = pop[i], pop[j]
        child = crossover(A, B, nbs, n, rng)
        m0 = len(child)
        S = run_rtabu(child, child_secs, rng.randrange(1 << 30), tmpdir, q)
        if not relaxed(S, nbs):
            say('gen %d: invalid child output, skipped' % gen)
            continue
        if S in pop:
            continue
        w = min(range(len(pop)), key=lambda k: len(pop[k]))
        if len(S) >= len(pop[w]):
            pop[w] = S
        if len(S) > len(best):
            best = S
            write_set(outf, best)
            say('gen %d: new best %d (start %d, parents %d %d) %.0f s' % (gen, len(best), m0, len(A), len(B),
                                                                       time.time() - t0))
        if gen % 10 == 0:
            say('gen %d: pop sizes %s, best %d, %.0f s' % (gen, sorted(len(s) for s in pop), len(best),
                                                        time.time() - t0))
    say('done: best %d after %d generations, %.0f s' % (len(best), gen, time.time() - t0))
    print('best %d gens %d' % (len(best), gen))


if __name__ == '__main__':
    main()
