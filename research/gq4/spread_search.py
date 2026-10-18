"""Large partial spreads of Q(4,q): iterated local search on the line conflict graph.

Two lines conflict when they share a point. A partial spread is an independent set in that graph. The search itself
is spread_ils.c (compiled with cc -O2 into a temp dir); this file builds the graph, runs the search for a set time,
re-checks the answer and saves it.

usage: python3 spread_search.py q seconds [seed]
writes: spreads/spread_q{q}_s{size}.json, a JSON list of line indices into q4(q)'s `lines`.
"""
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from gq_clones import q4  # noqa: E402


def conflict_pairs(lines):
    """Pairs (a, b), a < b, of lines that share a point. Two distinct lines share at most one point, so no repeats."""
    through = {}
    for j, L in enumerate(lines):
        for p in L:
            through.setdefault(p, []).append(j)
    pairs = []
    for js in through.values():
        for x in range(len(js)):
            for y in range(x + 1, len(js)):
                pairs.append((js[x], js[y]))
    return pairs


def check_spread(lines, chosen):
    """Raise unless chosen is a list of distinct line indices whose lines are pairwise disjoint."""
    if len(set(chosen)) != len(chosen):
        raise ValueError('repeated line index')
    used = set()
    for j in chosen:
        if used & lines[j]:
            raise ValueError(f'line {j} shares a point with an earlier line')
        used |= lines[j]


def main():
    q = int(sys.argv[1])
    seconds = float(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1

    t0 = time.time()
    pts, lines, ovoid = q4(q)
    pairs = conflict_pairs(lines)
    print(f'q={q} seed={seed}: {len(lines)} lines, {len(pairs)} conflicts, built in {time.time() - t0:.1f}s',
          flush=True)

    work = Path(tempfile.mkdtemp(prefix=f'spread_q{q}_s{seed}_'))
    try:
        exe = work / 'spread_ils'
        subprocess.run(['cc', '-O2', '-o', str(exe), str(HERE / 'spread_ils.c')], check=True)
        graph = work / 'graph.txt'
        result = work / 'best.txt'
        with graph.open('w') as f:
            f.write(f'{len(lines)} {len(pairs)}\n')
            f.writelines(f'{a} {b}\n' for a, b in pairs)

        proc = subprocess.Popen([str(exe), str(graph), str(seconds), str(seed), str(result)],
                                stdout=subprocess.PIPE, text=True)
        summary = {}
        for line in proc.stdout:
            line = line.rstrip()
            print(f'q={q} seed={seed} {line}', flush=True)
            key, _, value = line.partition(' ')
            if key in ('BEST', 'PERTURBS', 'SWAPS', 'SECONDS', 'RATE'):
                summary[key] = value
        if proc.wait() != 0:
            raise SystemExit(f'spread_ils failed with exit code {proc.returncode}')

        values = result.read_text().split()
        size = int(values[0])
        chosen = [int(x) for x in values[1:]]
        if len(chosen) != size:
            raise SystemExit(f'expected {size} lines in the result, found {len(chosen)}')
        check_spread(lines, chosen)

        dest = HERE / 'spreads' / f'spread_q{q}_s{size}.json'
        dest.parent.mkdir(exist_ok=True)
        dest.write_text(json.dumps(sorted(chosen)))
        print(f'q={q} seed={seed} FINAL size={size} checked disjoint, saved {dest}', flush=True)
        print(f'q={q} seed={seed} RATE perturbations/s={summary.get("RATE")} '
              f'swaps={summary.get("SWAPS")} perturbations={summary.get("PERTURBS")} '
              f'seconds={summary.get("SECONDS")}', flush=True)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == '__main__':
    main()
