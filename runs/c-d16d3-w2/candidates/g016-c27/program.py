import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy ball-cover vertex insertion (diameter D, bipartite, degree d).
#
# Let R = D-1 and ball(u) = vertices within distance R of u. A new vertex w on
# side s joined to a set N of opposite-side vertices is within distance D of every
# old vertex x exactly when x lies in ball(u) for some u in N. Adding w never
# shortens or breaks existing paths, so validity is preserved. When no insertion
# is possible, the engine adds a random edge between two spare-degree vertices on
# opposite sides. That can only shrink distances, so it also keeps validity.
# Arguments: d D seed budget. Reads "n m" plus edges on stdin, prints the graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXITER 20000

typedef uint64_t u64;

static int DEG_, R_, n_, cap_;
static int *deg_, *capadj_, *col_;
static int **adj_;
static u64 rs_;

static u64 rnd_(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}

static int rndint_(int k) {
    return (int)(rnd_() % (u64)k);
}

static int popc_(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void push_(int u, int v) {
    if (deg_[u] == capadj_[u]) {
        int nc = capadj_[u] * 2 + 4;
        int *p = (int *)realloc(adj_[u], sizeof(int) * (size_t)nc);
        if (!p) exit(1);
        adj_[u] = p;
        capadj_[u] = nc;
    }
    adj_[u][deg_[u]++] = v;
}

static int has_(int u, int v) {
    for (int i = 0; i < deg_[u]; i++)
        if (adj_[u][i] == v) return 1;
    return 0;
}

static void link_(int u, int v) {
    push_(u, v);
    push_(v, u);
}

static void read_input(void) {
    long n = 0, m = 0;
    if (scanf("%ld %ld", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0) n = 0;
    n_ = (int)n;
    cap_ = n_ + MAXITER + 8;
    deg_ = (int *)calloc((size_t)cap_, sizeof(int));
    capadj_ = (int *)calloc((size_t)cap_, sizeof(int));
    col_ = (int *)calloc((size_t)cap_, sizeof(int));
    adj_ = (int **)calloc((size_t)cap_, sizeof(int *));
    for (long i = 0; i < m; i++) {
        long a, b;
        if (scanf("%ld %ld", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n_ || b >= n_ || a == b) continue;
        if (has_((int)a, (int)b)) continue;
        link_((int)a, (int)b);
    }
    /* BFS 2-colouring of the input. */
    int *q = (int *)malloc(sizeof(int) * (size_t)cap_);
    for (int i = 0; i < n_; i++) col_[i] = -1;
    for (int s = 0; s < n_; s++) {
        if (col_[s] != -1) continue;
        int head = 0, tail = 0;
        col_[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg_[u]; i++) {
                int v = adj_[u][i];
                if (col_[v] == -1) {
                    col_[v] = 1 - col_[u];
                    q[tail++] = v;
                }
            }
        }
    }
    free(q);
}

/* ball[v*W + w]: bitmask of vertices within distance R_ of v. */
static u64 *ball_masks(int W) {
    int n = n_;
    u64 *a = (u64 *)calloc((size_t)n * (size_t)W, sizeof(u64));
    u64 *b = (u64 *)calloc((size_t)n * (size_t)W, sizeof(u64));
    for (int v = 0; v < n; v++)
        a[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < R_; r++) {
        for (int v = 0; v < n; v++) {
            u64 *bv = b + (size_t)v * W;
            memcpy(bv, a + (size_t)v * W, sizeof(u64) * (size_t)W);
            for (int i = 0; i < deg_[v]; i++) {
                const u64 *au = a + (size_t)adj_[v][i] * W;
                for (int w = 0; w < W; w++) bv[w] |= au[w];
            }
        }
        u64 *t = a;
        a = b;
        b = t;
    }
    free(b);
    return a;
}

static int covers_(const u64 *cov, const u64 *full, int W) {
    for (int w = 0; w < W; w++)
        if (cov[w] != full[w]) return 0;
    return 1;
}

/* Try to insert one new vertex by greedy set cover of all vertices with balls. */
static int try_insert(const u64 *ball, int W, const u64 *full) {
    int n = n_, d = DEG_;
    int ok = 0;
    int *cand = (int *)malloc(sizeof(int) * (size_t)(n + 1));
    int *chosen = (int *)malloc(sizeof(int) * (size_t)(d + 2));
    u64 *cov = (u64 *)malloc(sizeof(u64) * (size_t)W);
    int first = rndint_(2);
    for (int si = 0; si < 2 && !ok; si++) {
        int s = (si + first) & 1;
        for (int att = 0; att < 3 && !ok; att++) {
            int nc = 0;
            for (int v = 0; v < n; v++)
                if (col_[v] == 1 - s && deg_[v] < d) cand[nc++] = v;
            if (nc == 0) break;
            for (int i = nc - 1; i > 0; i--) {
                int j = rndint_(i + 1);
                int t = cand[i];
                cand[i] = cand[j];
                cand[j] = t;
            }
            memset(cov, 0, sizeof(u64) * (size_t)W);
            int nch = 0;
            while (nch < d) {
                if (covers_(cov, full, W)) break;
                int best = 0, bi = -1;
                for (int i = 0; i < nc; i++) {
                    const u64 *bu = ball + (size_t)cand[i] * W;
                    int g = 0;
                    for (int w = 0; w < W; w++) g += popc_(bu[w] & ~cov[w]);
                    if (g > best) {
                        best = g;
                        bi = i;
                    }
                }
                if (bi < 0) break;
                int pick = cand[bi];
                chosen[nch++] = pick;
                const u64 *bp = ball + (size_t)pick * W;
                for (int w = 0; w < W; w++) cov[w] |= bp[w];
                cand[bi] = cand[--nc];
            }
            if (covers_(cov, full, W)) {
                int w = n_++;
                col_[w] = s;
                deg_[w] = 0;
                capadj_[w] = 0;
                adj_[w] = NULL;
                for (int k = 0; k < nch; k++) link_(chosen[k], w);
                ok = 1;
            }
        }
    }
    free(cand);
    free(chosen);
    free(cov);
    return ok;
}

/* Add one random edge between spare-degree vertices on opposite sides. */
static void add_spare(void) {
    int n = n_, d = DEG_;
    int *A = (int *)malloc(sizeof(int) * (size_t)(n + 1));
    int *B = (int *)malloc(sizeof(int) * (size_t)(n + 1));
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg_[v] < d) {
            if (col_[v] == 0) A[na++] = v;
            else B[nb++] = v;
        }
    }
    if (na > 0 && nb > 0) {
        for (int t = 0; t < 40; t++) {
            int u = A[rndint_(na)];
            int v = B[rndint_(nb)];
            if (!has_(u, v)) {
                link_(u, v);
                break;
            }
        }
    }
    free(A);
    free(B);
}

static void emit(void) {
    long m = 0;
    for (int u = 0; u < n_; u++)
        for (int i = 0; i < deg_[u]; i++)
            if (adj_[u][i] > u) m++;
    printf("%d %ld\n", n_, m);
    for (int u = 0; u < n_; u++)
        for (int i = 0; i < deg_[u]; i++)
            if (adj_[u][i] > u) printf("%d %d\n", u, adj_[u][i]);
}

int main(int argc, char **argv) {
    DEG_ = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    long budget = argc > 4 ? atol(argv[4]) : 2000;
    if (budget < 0) budget = 0;
    if (budget > MAXITER) budget = MAXITER;
    rs_ = (u64)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs_ == 0) rs_ = 1;

    read_input();
    R_ = D - 1;
    if (n_ > 0 && R_ >= 1 && DEG_ >= 1) {
        int fails = 0;
        for (long it = 0; it < budget && fails < 400; it++) {
            int W = (n_ + 63) / 64;
            u64 *full = (u64 *)calloc((size_t)W, sizeof(u64));
            for (int v = 0; v < n_; v++)
                full[v >> 6] |= 1ULL << (v & 63);
            u64 *ball = ball_masks(W);
            int ins = try_insert(ball, W, full);
            free(ball);
            free(full);
            if (ins) {
                fails = 0;
            } else {
                fails++;
                add_spare();
            }
        }
    }
    emit();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S such
# that every line contains at most s points of S and every point lies on at most
# s lines indexed by S. For each P in S add a new A-vertex joined to the q+1 lines
# through P; for each j in S add a new B-vertex joined to the q+1 points on line j.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cyclic Haar graphs from difference covers (diameter 3).
#
# For S a k-subset of Z_m, H(m, S) joins a_i to b_{i+s} for s in S. If every
# nonzero residue is a difference of S, then A-A pairs are within distance 2,
# and S-S+S = Z_m gives A-B pairs within distance 3.
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    """Return (cnt, zeros): cnt[x] = #ordered pairs with difference x; zeros = #{x != 0 : cnt[x] = 0}."""
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    """Replace S[i] by y, updating cnt and the zero count. Returns the new zero count."""
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            a = (old - t) % m
            b = (t - old) % m
            cnt[a] -= 1
            if cnt[a] == 0:
                zeros += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            a = (y - t) % m
            b = (t - y) % m
            if cnt[a] == 0:
                zeros -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                zeros -= 1
            cnt[b] += 1
    return zeros


def _cover_search(k, m, deadline, rng):
    """Find a k-subset S of Z_m whose nonzero differences cover Z_m minus {0}; return sorted S or None."""
    if k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    cnt, zeros = _diff_counts(S, m)
    T = 0.3
    moves = 0
    while zeros > 0:
        moves += 1
        if moves % 512 == 0 and time.monotonic() > deadline:
            return None
        if moves % 200000 == 0:
            S = rng.sample(range(m), k)
            cnt, zeros = _diff_counts(S, m)
            continue
        i = rng.randrange(k)
        y = rng.randrange(m)
        if y in S:
            continue
        old = S[i]
        z = _move(S, cnt, i, y, m, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _move(S, cnt, i, old, m, z)
    return sorted(S)


def _difference_graph(d, deadline, rng):
    """Largest cyclic Haar graph H(m, S) with |S| = d found before the deadline, as (n, edges), or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        S = _cover_search(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# Glue: run the C ball-cover augmenter on a start graph.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, seed, deadline, budget=20000):
    """Return (n, edges) from the C augmenter, or None if it fails or runs out of time."""
    if n < 1:
        return None
    left = deadline - time.monotonic()
    if left < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=(n, edges), timeout=left)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # New: greedy ball-cover vertex insertion in C on the best arc graph.
        if arcs:
            r = _augment(arcs[0][0], arcs[0][1], d, D, seed, start + 0.25 * time_limit)
            if r is not None:
                consider(r[0], r[1])

        if D == 3:
            hg = _difference_graph(d, start + 0.55 * time_limit, rng)
            if hg is not None:
                consider(hg[0], hg[1])

    # Final augmentation of whatever is currently best (cheap if nothing fits).
    r = _augment(best_n, best[1], d, D, seed + 1, start + 0.80 * time_limit)
    if r is not None:
        consider(r[0], r[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
