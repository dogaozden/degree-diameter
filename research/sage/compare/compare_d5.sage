r"""
Compare the diameter-5 Sage graphs with the lab's builders and record files.

  (1) (7,5) 1,200: d5_haar_7_5_1200.sage against the edge list written by research/frontier/build_haar2.py (which builds
      SL(2,5) x Z_5 from its definition); the vertex index of build_haar2.py is rank(M)*5 + z with the matrices in sorted
      order; EXACT edge-set equality.
  (2) (5,5) 360: d5_lift_5_5_360.sage against the edge list written by research/beyond-haar-d5/records/
      build_d5D5_n360_z15s3.py (EXACT, same vertex numbering rule a*90 + index of g) and, as graphs, against the record
      file d5D5_n360_lift_g90_6.edges (built from GAP's multiplication table; G.is_isomorphic).
  (3) (5,5) 384: d5_lift_5_5_384.sage against the record files d5D5_n384_a1_g96_31.edges and d5D5_n384_a2_g96_17.edges
      (vertex = base_index*96 + element index; EXACT edge-set equality).

Run from research/sage:  sage compare/compare_d5.sage
"""
import sys, os, subprocess, tempfile
REPO = os.path.abspath(os.path.join(os.path.abspath('.'), '..', '..'))
NO_AUTO_CHECK = True


def read_edges(path):
    lines = [l.split() for l in open(path).read().split('\n') if l.strip()]
    n = int(lines[0][0])
    return n, {frozenset(map(int, l)) for l in lines[1:]}


def compare_1200():
    load('d5_haar_7_5_1200.sage')
    tmp = tempfile.mktemp(suffix='.edges')
    rec = os.path.join(REPO, 'research/beyond-haar-d5/records/d7D5_n1200_haar_sl5xc5.txt')
    subprocess.run([sys.executable, os.path.join(REPO, 'research/frontier/build_haar2.py'), rec, tmp],
                   check=True, capture_output=True)
    n, E_py = read_edges(tmp)
    els = sl2_times_cyclic(5)
    mats = sorted({g[0] for g in els})                   # rank in the sorted keys ((a q + b) q + c) q + d = lexicographic
    idx = {g: mats.index(g[0]) * 5 + g[1] for g in els}
    G = build_d5_haar_7_5_1200()
    E = {frozenset((idx[u[1]], 600 + idx[v[1]])) if u[0] == 0 else frozenset((idx[v[1]], 600 + idx[u[1]]))
         for u, v in G.edges(sort=False, labels=False)}
    print(f'  (7,5) 1200: build_haar2.py edge list ({n} vertices, {len(E_py)} edges) vs Sage ({G.order()} vertices, '
          f'{len(E)} edges): exact edge-set equality {E == E_py}')
    os.remove(tmp)
    return E == E_py


def compare_360():
    load('d5_lift_5_5_360.sage')
    tmp = tempfile.mktemp(suffix='.edges')
    subprocess.run([sys.executable, os.path.join(REPO, 'research/beyond-haar-d5/records/build_d5D5_n360_z15s3.py'), tmp],
                   check=True, capture_output=True)
    n, E_py = read_edges(tmp)
    els = c15_times_s3()
    idx = {g: k for k, g in enumerate(els)}
    base = {'A0': 0, 'A1': 1, 'B0': 2, 'B1': 3}
    G = build_d5_lift_5_5_360()
    E = {frozenset((base[u[1]] * 90 + idx[u[2]], base[v[1]] * 90 + idx[v[2]])) for u, v in G.edges(sort=False, labels=False)}
    same = (E == E_py)
    print(f'  (5,5) 360: build_d5D5_n360_z15s3.py edge list ({n} vertices, {len(E_py)} edges) vs Sage: exact edge-set equality {same}')
    ok = same
    for f in ('d5D5_n360_lift_g90_6.edges',):    # (d5D5_n360b_lift_g90_6.edges is a second, different 360 solution)
        n2, E2 = read_edges(os.path.join(REPO, 'research/beyond-haar-d5/records', f))
        R = Graph([tuple(e) for e in E2])
        iso = G.is_isomorphic(R)
        print(f'  (5,5) 360: record file {f} ({n2} vertices, {len(E2)} edges): isomorphic to the Sage graph: {iso}')
        ok &= iso
    os.remove(tmp)
    return ok


def compare_384():
    load('d5_lift_5_5_384.sage')
    base = {'A0': 0, 'A1': 1, 'B0': 2, 'B1': 3}
    ok = True
    for variant, i, f in (('a1_g96_31', 31, 'd5D5_n384_a1_g96_31.edges'), ('a2_g96_17', 17, 'd5D5_n384_a2_g96_17.edges')):
        n, E_rec = read_edges(os.path.join(REPO, 'research/beyond-haar-d5b/records', f))
        elems, mul, _ = small_group_96(i)
        idx = {e: k for k, e in enumerate(elems)}
        G = build_d5_lift_5_5_384(variant)
        E = {frozenset((base[u[1]] * 96 + idx[u[2]], base[v[1]] * 96 + idx[v[2]])) for u, v in G.edges(sort=False, labels=False)}
        same = (E == E_rec)
        print(f'  (5,5) 384 {variant}: record file {f} ({n} vertices, {len(E_rec)} edges) vs Sage ({G.order()} vertices, '
              f'{len(E)} edges): exact edge-set equality {same}')
        ok &= same
    return ok


ok = True
ok &= compare_1200()
ok &= compare_360()
ok &= compare_384()
print('ALL COMPARISONS PASS' if ok else 'SOME COMPARISON FAILED')
