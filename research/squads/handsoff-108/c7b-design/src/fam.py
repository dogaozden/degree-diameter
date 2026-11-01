# fam.py (worker c7b): write lift3-format solutions for formula families and evaluate them with hexeval (IN=..., ITERS=0).
# Point cost = RESULT cost - 100 * dup (dup = parallel edges, penalised inside hexeval).
# usage examples (from the c7b folder):
#   python3 -I src/fam.py const 3 24 ...   (see main() below)
import sys, os, random, subprocess, struct

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')


def read_hex(q):
    with open(os.path.join(HERE, 'hex', 'hex_q%d.bin' % q), 'rb') as f:
        qq, N, L = struct.unpack('<iii', f.read(12))
        pl = struct.unpack('<%di' % (L * (q + 1)), f.read(4 * L * (q + 1)))
    return N, [pl[k * (q + 1):(k + 1) * (q + 1)] for k in range(L)]


def write_sol(fn, q, m, J, sig, mv, hv):
    with open(fn, 'w') as f:
        f.write('%d %d %d %d %d\ncyc %d\n' % (q, J, m, 8, 0, m))
        for t in range(J):
            f.write(' '.join(map(str, sig[t])) + '\n')
        for t in range(J):
            f.write(' '.join(map(str, mv[t])) + '\n')
        f.write(' '.join(map(str, hv)) + '\n')


def evaluate(q, m, fn):
    """point cost (uncovered walk triples) of the solution file fn, via hexeval with ITERS=0"""
    env = dict(os.environ, IN=fn, ITERS='0', M=str(m), HZERO='0', J='2')
    r = subprocess.run([os.path.join(HERE, 'src', 'hexeval'), str(q)], env=env, capture_output=True, text=True,
                       timeout=900)
    for line in r.stdout.splitlines():
        if line.startswith('RESULT'):
            w = line.split()
            cost, dup = int(w[-3]), int(w[-1])
            return cost - 100 * dup, dup
    raise RuntimeError(r.stderr[-500:])


def random_matchings(N, J, rng):
    sig = []
    for t in range(J):
        perm = list(range(N))
        rng.shuffle(perm)
        sig.append(perm)
    return sig


if __name__ == '__main__':
    # const: hexagon voltages 0, matching t voltage constant c_t on every point, random perfect matchings
    # usage: fam.py const Q M SEED A B   (one (a,b) pair)
    #        fam.py constscan Q M SEED   (all (a,b) in Z_M^2 with a <= b, prints the best few)
    mode = sys.argv[1]
    q, m, seed = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    N, lines = read_hex(q)
    Q1 = q + 1
    rng = random.Random(seed)
    sig = random_matchings(N, 2, rng)
    hv = [0] * (N * Q1)
    tmp = os.path.join(HERE, 'runs', 'fam_tmp_q%d_m%d_s%d.sol' % (q, m, seed))
    if mode == 'const':
        a, b = int(sys.argv[5]), int(sys.argv[6])
        mv = [[a] * N, [b] * N]
        write_sol(tmp, q, m, 2, sig, mv, hv)
        print('q=%d m=%d seed=%d a=%d b=%d point_cost=%d dup=%d' % ((q, m, seed, a, b) + evaluate(q, m, tmp)))
    elif mode == 'constscan':
        res = []
        for a in range(m):
            for b in range(a, m):
                mv = [[a] * N, [b] * N]
                write_sol(tmp, q, m, 2, sig, mv, hv)
                pc, dup = evaluate(q, m, tmp)
                res.append((pc + 100 * dup, pc, dup, a, b))
        res.sort()
        print('q=%d m=%d seed=%d pairs=%d best(total,point,dup,a,b)=%s' % (q, m, seed, len(res), res[:5]))
