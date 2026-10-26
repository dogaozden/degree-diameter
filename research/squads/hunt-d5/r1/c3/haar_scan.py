"""Haar graphs H(G,{e,a,b}) over all groups of order m (SmallGroups via gapgroup tables)."""
import subprocess, sys, struct, array, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ctrl

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, '..', '..', 'tools')
TABDIR = os.path.join(HERE, 'tab')
os.makedirs(TABDIR, exist_ok=True)

def load_table(path):
    data = open(path, 'rb').read()
    N = struct.unpack('<i', data[:4])[0]
    T = array.array('H')
    T.frombytes(data[4:4 + 2 * N * N])
    return N, list(T)

def groups_of(n):
    out = subprocess.run(['python3', os.path.join(TOOLS, 'gapgroup.py'), 'list', str(n)],
                         capture_output=True, text=True, timeout=300).stdout.split('\n')
    res = []
    for line in out:
        p = line.split()
        if len(p) >= 2 and p[0] == str(n):
            res.append((int(p[1]), line))
    return res

def table_for(n, i):
    path = os.path.join(TABDIR, f'g{n}_{i}.bin')
    if not os.path.exists(path):
        subprocess.run(['timeout', '120', 'nice', '-n', '10', 'python3', os.path.join(TOOLS, 'gapgroup.py'),
                        'table', str(n), str(i), path], check=True, capture_output=True, timeout=200)
    return path

if __name__ == '__main__':
    ms = [int(x) for x in sys.argv[1:]]
    best_overall = {}
    for m in ms:
        t0 = time.time()
        best = (10**9, None, None)
        glist = groups_of(m)
        found = []
        for i, line in glist:
            N, T = load_table(table_for(m, i))
            assert N == m
            for a, b in itertools.combinations(range(1, m), 2):
                S = [0, a, b]
                adj = ctrl.haar_adj(m, N, T, S)
                c = ctrl.cost(adj, m)
                if c < best[0]:
                    best = (c, f'SmallGroup({m},{i}) [{line.split(None, 3)[3]}] S={S}', adj)
                if c == 0:
                    found.append((i, S))
        c, desc, adj = best
        if adj is not None:
            c4 = sum(ctrl.c4_count(adj, v) for v in range(2 * m)) / (2 * m)
        else:
            c4 = 0
        print(f'm={m} groups={len(glist)} best_cost={c} at {desc} mean_c4_per_vertex={c4:.2f} zero_hits={len(found)} '
              f'time={time.time()-t0:.1f}s', flush=True)
        if c == 0:
            ctrl.write_edges(os.path.join(HERE, f'ctrl_m{m}.edges'), m, adj)
            print('  saved', f'ctrl_m{m}.edges', flush=True)
