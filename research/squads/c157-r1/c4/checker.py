#!/usr/bin/env python3
"""Checker for hub graphs (file format of research/d15D7/pg27.hg).

File: first line "K m", then m lines "j k" meaning line-side hub j ~ point-side hub k
(0 <= j, k < K, no repeated pair). Checks:
  (i)   every vertex, on both sides, has degree <= MAXDEG (= 8);
  (ii)  any two distinct line-side hubs have a common neighbour (a point-side hub);
  (iii) any two distinct point-side hubs have a common neighbour (a line-side hub).
Also checks indices, the header and the number of lines.

Usage: python3 checker.py FILE [FILE ...]   (exit status 0 iff every file passes)
"""
import sys

MAXDEG = 8


def check_graph(K, edges, maxdeg=MAXDEG):
    """Check a hub graph given as K and an iterable of (j, k) pairs.
    Returns (ok, info) where info is a dict with the counts and the first problems found."""
    problems = []
    seen = set()
    nA = [0] * K  # nA[j]: bitmask of point-side hubs adjacent to line-side hub j
    nB = [0] * K  # nB[k]: bitmask of line-side hubs adjacent to point-side hub k
    m = 0
    for j, k in edges:
        m += 1
        if not (0 <= j < K and 0 <= k < K):
            problems.append(f"index out of range: {j} {k}")
            continue
        if (j, k) in seen:
            problems.append(f"repeated pair: {j} {k}")
            continue
        seen.add((j, k))
        nA[j] |= 1 << k
        nB[k] |= 1 << j
    degA = [x.bit_count() for x in nA]
    degB = [x.bit_count() for x in nB]
    bad_deg = [f"line-side {j} has degree {d}" for j, d in enumerate(degA) if d > maxdeg]
    bad_deg += [f"point-side {k} has degree {d}" for k, d in enumerate(degB) if d > maxdeg]
    bad_A = [(i, j) for i in range(K) for j in range(i + 1, K) if not (nA[i] & nA[j])]
    bad_B = [(i, j) for i in range(K) for j in range(i + 1, K) if not (nB[i] & nB[j])]
    ok = not (problems or bad_deg or bad_A or bad_B)
    info = {
        "K": K,
        "m": m,
        "maxdeg": max(degA + degB) if K else 0,
        "unpaired_line_hubs": len(bad_A),
        "unpaired_point_hubs": len(bad_B),
        "degree_violations": len(bad_deg),
        "problems": (problems + bad_deg + [f"line hubs {p} have no common neighbour" for p in bad_A[:3]]
                     + [f"point hubs {p} have no common neighbour" for p in bad_B[:3]])[:8],
    }
    return ok, info


def read_hg(path):
    """Parse a .hg file. Returns (K, edges, header_problems)."""
    with open(path) as f:
        toks = f.read().split()
    if len(toks) < 2:
        raise ValueError("empty file")
    K, m = int(toks[0]), int(toks[1])
    rest = toks[2:]
    problems = []
    if len(rest) != 2 * m:
        problems.append(f"header says m={m} but file has {len(rest) // 2} pairs (odd token count: {len(rest) % 2})")
    edges = [(int(rest[2 * i]), int(rest[2 * i + 1])) for i in range(len(rest) // 2)]
    return K, edges, problems


def check_file(path):
    K, edges, header_problems = read_hg(path)
    ok, info = check_graph(K, edges)
    if header_problems:
        ok = False
        info["problems"] = header_problems + info["problems"]
    return ok, info


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    all_ok = True
    for path in argv:
        try:
            ok, info = check_file(path)
        except Exception as e:  # malformed file counts as a failure
            ok, info = False, {"problems": [f"unreadable: {e}"]}
        all_ok = all_ok and ok
        if ok:
            print(f"OK   {path}  K={info['K']} m={info['m']} maxdeg={info['maxdeg']}")
        else:
            print(f"FAIL {path}  K={info.get('K')} m={info.get('m')} maxdeg={info.get('maxdeg')} "
                  f"unpaired_line_hubs={info.get('unpaired_line_hubs')} "
                  f"unpaired_point_hubs={info.get('unpaired_point_hubs')} "
                  f"degree_violations={info.get('degree_violations')}")
            for p in info.get("problems", []):
                print(f"     - {p}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
