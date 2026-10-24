#!/usr/bin/env python3
"""B4 census: reads randorb_*.log in this folder (written by driver.sh / one.sh) and writes census.md and levels_raw.txt.

BFS layer counts from the printed `levels:` values. haar_sym's bfs() starts on side A with cnt[A] = 1 (identity) and
prints lev[h] = cumulative number of distinct elements on the side reached at step h+1 (sides alternate). So with
D = 10 (9 steps):
  layer 1 = lev[0]          (= 11 = words)
  layer 2 = lev[1] - 1      (identity removed)
  layer L = lev[L-1] - lev[L-3]   for L >= 3
Non-backtracking words at level L: 11 * 10^(L-1).
Random-words baseline: a layer of w = words(L) uniform draws into the (N - prev) still-uncovered elements of the side
hits (N - prev) * (1 - exp(-w / N)) distinct new elements, where prev = elements already covered on that side (observed).
loss = 1 - layer / words; excess = baseline loss - observed loss (the part of the loss not explained by saturation).
"""
import glob
import os
import re
import statistics
import math

HERE = os.path.dirname(os.path.abspath(__file__))
DEG = 11
LEVELS_SHOWN = (6, 7, 8)


def words(L):
    return DEG * 10 ** (L - 1)


def parse_log(path):
    txt = open(path, encoding="utf-8", errors="replace").read()
    out = {"path": path, "tag": os.path.basename(path)[len("randorb_"):-len(".log")]}
    m = re.search(r"RANDORB d=\d+ D=\d+ group=(.*?) x Z_(\d+) N=(\d+) k=(\d+) m=(\d+) f=(\d+) fix=(\d+) samples=(\d+) "
                  r"min=(\d+) p1=\d+ p10=\d+ median=(\d+) mean=([\d.]+) var=[\d.]+ mu=([\d.]+)", txt)
    if m:
        out.update(group=m.group(1).strip(), n=int(m.group(2)), N=int(m.group(3)), k=int(m.group(4)),
                   fix=int(m.group(7)), samples=int(m.group(8)), median=int(m.group(10)), mu=float(m.group(12)))
    m = re.search(r"ORBIT k=\d+ m=\d+ f=\d+: \|Fix\(alpha\)\| = \d+ \(\+e\); mu = ([\d.]+), mu/k = ([\d.]+)", txt)
    if m:
        out.update(mu_fixed=float(m.group(1)), mu_over_k=float(m.group(2)))
    m = re.search(r"B4_INSIDE_SECONDS ([\d.]+) rc=(\d+)", txt)
    out["inside_s"] = float(m.group(1)) if m else None
    out["rc"] = int(m.group(2)) if m else None
    out["levels"] = [tuple(int(x) for x in re.findall(r"\d+", lv)) for lv in
                     re.findall(r"^levels:((?: \d+){9}) cost \d+$", txt, flags=re.M)]
    out["costs"] = [int(c) for c in re.findall(r"^levels:(?: \d+){9} cost (\d+)$", txt, flags=re.M)]
    out["raw_levels_lines"] = re.findall(r"^levels:.*$", txt, flags=re.M)
    out["error"] = None if out["levels"] else (txt.strip().splitlines()[-1] if txt.strip() else "empty log")
    return out


def per_sample(N, lev):
    """Return dict L -> (layer, words, loss, baseline_loss, excess) for L = 1..9 for one sample."""
    layers = {1: lev[0], 2: lev[1] - 1}
    for L in range(3, 10):
        layers[L] = lev[L - 1] - lev[L - 3]
    prev = {1: 0, 2: 1}
    for L in range(3, 10):
        prev[L] = lev[L - 3]
    res = {}
    for L in range(1, 10):
        w = words(L)
        base_new = (N - prev[L]) * (1.0 - math.exp(-w / N))
        loss = 1.0 - layers[L] / w
        base_loss = 1.0 - base_new / w
        res[L] = (layers[L], w, loss, base_loss, base_loss - loss)
    return res


def median3(xs):
    return statistics.median(xs) if xs else float("nan")


def main():
    logs = sorted(glob.glob(os.path.join(HERE, "randorb_*.log")))
    groups = []
    for p in logs:
        g = parse_log(p)
        if g.get("error") or not g.get("levels"):
            groups.append(g)
            continue
        N = g["N"]
        samples = [per_sample(N, lev) for lev in g["levels"]]
        g["samples"] = samples
        g["med_loss"] = {L: median3([s[L][2] for s in samples]) for L in range(1, 10)}
        g["med_base"] = {L: median3([s[L][3] for s in samples]) for L in range(1, 10)}
        g["med_excess"] = {L: median3([s[L][4] for s in samples]) for L in range(1, 10)}
        g["med_layer"] = {L: median3([s[L][0] for s in samples]) for L in range(1, 10)}
        g["mean678"] = sum(g["med_loss"][L] for L in LEVELS_SHOWN) / len(LEVELS_SHOWN)
        g["base678"] = sum(g["med_base"][L] for L in LEVELS_SHOWN) / len(LEVELS_SHOWN)
        g["excess678"] = sum(g["med_excess"][L] for L in LEVELS_SHOWN) / len(LEVELS_SHOWN)
        groups.append(g)

    ok = [g for g in groups if not g.get("error")]
    bad = [g for g in groups if g.get("error")]

    # raw levels dump (data only)
    with open(os.path.join(HERE, "levels_raw.txt"), "w") as f:
        f.write("# raw `levels:` lines from haar_sym (RANDORB=3 LEVELS=3, SECONDS=1, SEED=1, K=8), one block per cell\n")
        f.write("# values: lev[0..8] = cumulative distinct elements on the reached side after steps 1..9; then cost\n")
        for g in groups:
            f.write(f"\n## {g['tag']}\n")
            for line in g.get("raw_levels_lines", []):
                f.write(line + "\n")
            if g.get("error"):
                f.write(f"ERROR: {g['error']}\n")

    ok.sort(key=lambda g: -g["mean678"])
    ok_excess = sorted(ok, key=lambda g: -g["excess678"])
    rank_excess = {g["tag"]: i + 1 for i, g in enumerate(ok_excess)}

    def fmt_pct(x):
        return f"{100 * x:.2f}%"

    lines = []
    A = lines.append
    A("# B4 ball-growth census (card d11D10-r1 / B4)")
    A("")
    A("Setting: `ORBIT=\"k m f\" RANDORB=3 LEVELS=3 haar_sym 11 10 1 1 8 /dev/null GROUP n` (SECONDS=1, SEED=1, K=8), "
      "run through `gate.sh 121`, one run per cell. Each cell gives 3 random orbit-symmetric S (|S| = 11).")
    A("")
    A("Definitions (per BFS layer L, on the side the BFS reaches at that parity):")
    A("")
    A("- layer L = distinct elements first reached at distance L. From the printed cumulative `levels:` values lev[0..8]: "
      "layer 1 = lev[0], layer 2 = lev[1] - 1, layer L = lev[L-1] - lev[L-3] for L >= 3.")
    A("- words(L) = 11 * 10^(L-1), the non-backtracking walks of length L.")
    A("- loss = 1 - layer / words(L). This is the card's relative loss.")
    A("- baseline = loss of random words: a layer of words(L) uniform draws into the still-uncovered elements, "
      "(N - prev) * (1 - exp(-words/N)) distinct new elements, with prev = elements already covered on that side. "
      "excess = baseline - loss: the loss that is not explained by saturation of the side (N elements).")
    A("- median = median over the 3 samples (for 3 samples the middle value).")
    A("")
    A("## Ranking by loss at levels 6-8 (mean of the three median losses), most loss first")
    A("")
    A("| rank | cell | group | k | n | N | median cost (3 samples) | loss L6 | loss L7 | loss L8 | mean L6-8 | "
      "baseline mean L6-8 | excess mean L6-8 | excess rank | gate s |")
    A("|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for i, g in enumerate(ok):
        A(f"| {i + 1} | {g['tag']} | {g['group']} | {g['k']} | {g['n']} | {g['N']:,} | {g['median']} "
          f"({', '.join(str(c) for c in g['costs'])}) | {fmt_pct(g['med_loss'][6])} | {fmt_pct(g['med_loss'][7])} | "
          f"{fmt_pct(g['med_loss'][8])} | {fmt_pct(g['mean678'])} | {fmt_pct(g['base678'])} | "
          f"{fmt_pct(g['excess678'])} | {rank_excess[g['tag']]} | {g['inside_s'] if g['inside_s'] is not None else '-'} |")
    A("")
    if bad:
        A("Cells that did not finish (no levels lines):")
        for g in bad:
            A(f"- {g['tag']}: {g.get('error')}")
        A("")
    A("## Layer counts (median sample) against words")
    A("")
    A("| cell | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 |")
    A("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    A("| words | " + " | ".join(f"{words(L):,}" for L in range(1, 10)) + " |")
    for g in ok:
        A(f"| {g['tag']} | " + " | ".join(f"{g['med_layer'][L]:,.0f}" for L in range(1, 10)) + " |")
    A("")
    A("## Loss per level (median sample loss, all levels 3-8)")
    A("")
    A("| cell | L3 | L4 | L5 | L6 | L7 | L8 | baseline L6 | baseline L7 | baseline L8 |")
    A("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for g in ok:
        A(f"| {g['tag']} | " + " | ".join(fmt_pct(g['med_loss'][L]) for L in range(3, 9)) + " | "
          + " | ".join(fmt_pct(g['med_base'][L]) for L in (6, 7, 8)) + " |")
    A("")
    A("## Per-sample costs and mu")
    A("")
    A("| cell | mu (Poisson, from ORBIT line) | mu/k | fixed-point term | costs (3 samples) | inside-gate s | rc |")
    A("|---|---:|---:|---|---|---:|---:|")
    for g in ok:
        A(f"| {g['tag']} | {g.get('mu', float('nan')):.2f} | {g.get('mu_over_k', float('nan')):.2f} | "
          f"fix={g.get('fix')} | {', '.join(str(c) for c in g['costs'])} | "
          f"{g['inside_s'] if g['inside_s'] is not None else '-'} | {g.get('rc')} |")
    A("")
    open(os.path.join(HERE, "census.md"), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
