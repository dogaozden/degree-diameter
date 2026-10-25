#!/usr/bin/env python3
"""Card c6 (squad d10D8-r4): descent minima in research/d10D8/runs/*.log. ANALYSIS ONLY (no searches).

Run:  python3 -I /home/user/degree-diameter/research/squads/d10D8-r4/c6/analyze.py

Definitions
  fresh descent   = CHAIN line of a RESTARTAFTER=0 run (tags F15/F30/F60), or a RESTART=1 cycle, or the first cycle
                    of a reheat-from-best run that was not resumed. All start from random orbits.
  re-descent      = a reheat-from-best cycle (c>=1) of an older run; the first chain after a checkpoint resume
                    (starts from the saved best state); a CHAIN line of RESTARTAFTER=1/2 runs (descent + re-descents).
  improvement     = a descent whose minimum is below the run's global best before it started.
  Excluded        = ORBW=3 runs (ORBW3, C40: different objective), TMAX=3 (s1hot), FAST (1 line), RA3 (CHAIN lines lost
                    at the checkpoint resume), any chain/cycle of a resumed run that is not a CHAIN line.
  Cycle minima of older runs come from 30-s progress prints (approximate, +-30 s on durations).
  CHAIN minima and secs are exact (secs = wall time of the chain, single thread).
"""
import glob
import math
import os
import re

RUNS = '/home/user/degree-diameter/research/d10D8/runs'
PROG = re.compile(r'^t=(\d+) steps=(\d+) evals=(\d+) cost=(-?\d+) best=(-?\d+) T=([\d.]+)')
CHAIN = re.compile(r'^CHAIN (\d+) min (-?\d+) secs (\d+) evals (\d+)')
RESUMED = re.compile(r'^resumed from .*evals (\d+), (\d+) s spent, best (\d+)')
RESULT = re.compile(r'best=(\d+) evals=')
EXCLUDE_TAGS = {'ORBW3', 'C40', 'ORBW3_RA2', 'FAST', 'RA3'}


def parse_name(path):
    b = os.path.basename(path)[:-4]
    grp = 'prod' if 'prod_psl_7_sl_8_7' in b else ('psl23' if 'psl_23_97' in b else '?')
    rest = b.split('_orb3_', 1)[1]
    hot = 'hot' in rest
    tag = re.sub(r'_?s\d+(hot)?$', '', rest)
    return grp, tag, hot


def jump_median(rows):
    """Median (cost at a reheat print - best at previous print): ~0 reheat-from-best, large for fresh restarts."""
    js = []
    for k in range(1, len(rows)):
        if rows[k]['T'] > rows[k - 1]['T'] + 0.05:
            js.append(rows[k]['cost'] - rows[k - 1]['best'])
    if not js:
        return None
    js.sort()
    return js[len(js) // 2]


def cycles_of(rows, resumed):
    """Split a progress trace at reheats (T jumps up). Segment before the first reheat of a resumed run is skipped."""
    starts = [] if resumed else [0]
    for k in range(1, len(rows)):
        if rows[k]['T'] > rows[k - 1]['T'] + 0.05:
            starts.append(k)
    starts = sorted(set(starts))
    out = []
    for ci, s in enumerate(starts):
        e = starts[ci + 1] if ci + 1 < len(starts) else len(rows)
        if e <= s:
            continue
        if s == 0 and not resumed:
            t_start = 0.0
        else:
            t_start = (rows[s - 1]['t'] + rows[s]['t']) / 2
        t_end = (rows[e - 1]['t'] + rows[e]['t']) / 2 if e < len(rows) else rows[-1]['t']
        cmin = min(rows[k]['cost'] for k in range(s, e))
        best_before = rows[s - 1]['best'] if s > 0 else None
        best_after = rows[e]['best'] if e < len(rows) else None
        improved = best_before is not None and best_after is not None and best_after < best_before
        if improved:
            cmin = min(cmin, best_after)
        out.append(dict(index=ci, dur=t_end - t_start, min=cmin, improved=improved, complete=e < len(rows),
                        first=(ci == 0 and not resumed), best_before=best_before))
    return out


def collect():
    chains, cycles, results, files = [], [], [], []
    for path in sorted(glob.glob(os.path.join(RUNS, '*.log'))):
        grp, tag, hot = parse_name(path)
        name = os.path.basename(path)
        rows, ck_best, resumed = [], None, False
        seq = []  # ordered CHAIN records and resume markers
        for line in open(path, errors='replace'):
            m = RESUMED.match(line)
            if m:
                resumed = True
                ck_best = int(m[3])
                seq.append(('resume', ck_best))
                continue
            m = PROG.match(line)
            if m:
                rows.append(dict(t=int(m[1]), cost=int(m[4]), best=int(m[5]), T=float(m[6])))
            m = CHAIN.match(line)
            if m:
                seq.append(('chain', dict(min=int(m[2]), secs=int(m[3]), evals=int(m[4]))))
        res = None
        out_path = path[:-4] + '.out'
        if os.path.exists(out_path):
            for line in open(out_path, errors='replace'):
                m = RESULT.search(line)
                if m:
                    res = int(m[1])
        if res is not None:
            results.append(dict(file=name, grp=grp, best=res))
        if rows:
            results.append(dict(file=name, grp=grp, best=rows[-1]['best'], last_progress=True))
        info = dict(file=name, grp=grp, tag=tag, hot=hot, resumed=resumed, n_chain=0, n_prog=len(rows))
        excluded = hot or tag in EXCLUDE_TAGS
        info['excluded'] = excluded
        if any(k == 'chain' for k, _ in seq):
            # CHAIN-format run (RESTARTAFTER set). Track the run's global best to classify improvements.
            run_best = None
            after_resume = False
            seg_first = True
            for kind, val in seq:
                if kind == 'resume':
                    run_best = val if run_best is None else min(run_best, val)
                    after_resume = True
                    continue
                info['n_chain'] += 1
                from_ckpt = after_resume
                after_resume = False
                first_of_run = (run_best is None and not from_ckpt)
                rec = dict(file=name, grp=grp, tag=tag, min=val['min'], dur=val['secs'], evals=val['evals'],
                           best_before=run_best, first=first_of_run, from_ckpt=from_ckpt, excluded=excluded)
                if from_ckpt:
                    rec['kind'] = 'RB-chain'
                elif tag in ('F15', 'F30', 'F60'):
                    rec['kind'] = 'FRESH-chain'
                elif tag in ('R1', 'R2'):
                    rec['kind'] = f'RA{tag[1]}-chain'
                else:
                    rec['kind'] = 'other-chain'
                chains.append(rec)
                run_best = val['min'] if run_best is None else min(run_best, val['min'])
        elif rows:
            cyc = cycles_of(rows, resumed)
            jm = jump_median(rows)
            comp = sorted(c['dur'] for c in cyc if c['complete'])
            period = comp[len(comp) // 2] if comp else None
            # RESTART=1 (fresh orbits at each reheat): tag RESTART, and psl23 seed 3 (RESTART=1 per cells/d10D8.md section 6;
            # its cost jumps at reheats are never 0). The cost-jump median alone does not separate the classes (R60 has
            # median 12 but reheats from the best), so the class is set by name, and the jump median is only reported.
            cls = 'RESTART' if (tag == 'RESTART' or (grp == 'psl23' and tag == '' and '_orb3_s3' in name)) else 'FROMBEST'
            info.update(cls=cls, jump_median=jm, period=period)
            for c in cyc:
                kind = 'FRESH-cycle' if (cls == 'RESTART' or c['first']) else 'REDESC-cycle'
                cycles.append(dict(file=name, grp=grp, tag=tag, cls=cls, index=c['index'], min=c['min'],
                                   dur=c['dur'], complete=c['complete'], improved=c['improved'],
                                   best_before=c['best_before'], first=c['first'], kind=kind,
                                   period=period, excluded=excluded))
        files.append(info)
    return chains, cycles, results, files


def rate_ci(k, T):
    """Poisson rate per CPU-hour with an approximate 90% interval."""
    if T <= 0:
        return float('nan'), float('nan'), float('nan')
    lam = k / T
    lo = max(0.0, (k - 1.645 * math.sqrt(k)) / T) if k > 0 else 0.0
    hi = 2.30 / T if k == 0 else (k + 1.645 * math.sqrt(k)) / T
    return lam, lo, hi


def show_minima(label, recs, thresholds=(9, 10, 12, 15)):
    if not recs:
        print(f"{label}: none")
        return
    mins = sorted(r['min'] for r in recs)
    n = len(mins)
    T = sum(r['dur'] for r in recs) / 3600.0
    print(f"{label}: n={n} mean_secs={sum(r['dur'] for r in recs) / n:.1f} exposure_h={T:.3f}")
    print(f"   minima: {' '.join(str(m) for m in mins)}")
    for c in thresholds:
        k = sum(1 for m in mins if m <= c)
        lam, lo, hi = rate_ci(k, T)
        print(f"   P(min<={c:2d}) = {k}/{n} = {k / n:.3f}   {lam:.2f} per CPU-h (90% approx {lo:.2f}-{hi:.2f})")


def improvement_stats(label, recs):
    """Descents that beat the run's global best before they started (first-of-run and excluded runs skipped)."""
    use = [r for r in recs if r.get('best_before') is not None and not r.get('first') and not r.get('excluded')]
    if not use:
        print(f"{label}: no usable descents")
        return None
    T = sum(r['dur'] for r in use) / 3600.0
    imp = sum(1 for r in use if r['min'] < r['best_before'])
    ret = sum(1 for r in use if r['min'] == r['best_before'])
    fail = len(use) - imp - ret
    mean_best = sum(r['best_before'] for r in use) / len(use)
    lam, lo, hi = rate_ci(imp, T)
    print(f"{label}: n={len(use)} exposure_h={T:.3f} mean_s={sum(r['dur'] for r in use) / len(use):.0f} "
          f"mean_best_before={mean_best:.1f} | improve={imp} return_to_best={ret} worse={fail} | "
          f"improvements {lam:.2f} per CPU-h (90% approx {lo:.2f}-{hi:.2f})")
    return dict(n=len(use), T=T, imp=imp, rate=lam, mean_best=mean_best)


def truncated_geometric_mle(xs, ct):
    """Conditional MLE for p(x) ~ q^x on x = 0..ct given observed xs (all <= ct): returns (q, P(x=0 | x<=ct))."""
    n = len(xs)
    sx = sum(xs)
    best = None
    for k in range(-400, 401):
        lq = k / 100.0
        q = math.exp(lq)
        S = (ct + 1) if abs(lq) < 1e-12 else (1 - q ** (ct + 1)) / (1 - q)
        ll = sx * lq - n * math.log(S)
        if best is None or ll > best[0]:
            best = (ll, q, S)
    return best[1], 1.0 / best[2]


def truncated_poisson_mle(ks, kt):
    """Conditional MLE for lambda in p(k) ~ lambda^k/k! on k = 0..kt given observed ks (all <= kt)."""
    n = len(ks)
    sk = sum(ks)
    lfact = [math.lgamma(k + 1) for k in range(kt + 1)]
    best = None
    for i in range(1, 4001):
        lam = i / 200.0
        Z = sum(math.exp(k * math.log(lam) - lfact[k]) for k in range(kt + 1))
        ll = sk * math.log(lam) - n * math.log(Z)
        if best is None or ll > best[0]:
            best = (ll, lam, Z)
    return best[1], 1.0 / best[2]


def main():
    chains, cycles, results, files = collect()
    print("== inventory (excluded = ORBW=3 / TMAX=3 / FAST / RA3 runs, not used in the policy statistics) ==")
    for f in files:
        extra = f" class={f['cls']} period_s={f.get('period')} jump_med={f.get('jump_median')}" if 'cls' in f else ''
        print(f"{f['file'][:56]:56s} grp={f['grp']:5s} tag={f['tag'] or '(default)':9s} chains={f['n_chain']:2d} "
              f"prog={f['n_prog']:3d} resumed={f['resumed']!s:5s} excl={f['excluded']!s:5s}{extra}")

    use_chains = [c for c in chains if not c['excluded']]
    use_cycles = [c for c in cycles if not c['excluded']]
    groups = ['prod', 'psl23']

    print("\n== (a) fresh descent minima per group (exact CHAIN lines + RESTART=1 cycles + first cycles) ==")
    fresh = {}
    for g in groups:
        recs = [dict(min=c['min'], dur=c['dur'], policy=c['tag'], src='chain') for c in use_chains
                if c['grp'] == g and c['kind'] == 'FRESH-chain']
        recs += [dict(min=c['min'], dur=c['dur'], policy=('RESTART' if c['cls'] == 'RESTART' else 'FROMBEST-first'),
                      src='cycle') for c in use_cycles
                 if c['grp'] == g and c['kind'] == 'FRESH-cycle' and c['complete']]
        fresh[g] = recs
        for pol in ('F15', 'F30', 'F60', 'RESTART', 'FROMBEST-first'):
            sub = [r for r in recs if r['policy'] == pol or (pol == 'F15' and r['policy'] == 'F15')]
            if sub:
                show_minima(f"  {g:5s} {pol}", sub)
        show_minima(f"  {g:5s} ALL-FRESH", recs)

    print("\n== (c) re-descents from a good state (reheat-from-best cycles c>=1, checkpoint restarts, RA chains) ==")
    rd_c = [c for c in use_cycles if c['kind'] == 'REDESC-cycle']
    rb_chains = [c for c in use_chains if c['kind'] == 'RB-chain']
    ra_chains = [c for c in use_chains if c['kind'].startswith('RA')]
    fresh_chains = [c for c in use_chains if c['kind'] == 'FRESH-chain']
    fresh_cyc = [c for c in use_cycles if c['kind'] == 'FRESH-cycle']
    for g in groups:
        print(f"-- {g}")
        for lab, recs in (('FRESH chains (F15/F30/F60)', [c for c in fresh_chains if c['grp'] == g]),
                          ('FRESH RESTART=1 cycles', [c for c in fresh_cyc if c['grp'] == g and c['cls'] == 'RESTART']),
                          ('RA1 chains (descent+re-descent)', [c for c in ra_chains if c['grp'] == g and c['kind'] == 'RA1-chain']),
                          ('RA2 chains', [c for c in ra_chains if c['grp'] == g and c['kind'] == 'RA2-chain']),
                          ('REDESC reheat-from-best cycles (all periods)', [c for c in rd_c if c['grp'] == g]),
                          ('REDESC period ~150 s', [c for c in rd_c if c['grp'] == g and (c['period'] or 0) > 100]),
                          ('REDESC period ~60 s', [c for c in rd_c if c['grp'] == g and (c['period'] or 0) <= 100]),
                          ('RB chains (checkpoint restart from best)', [c for c in rb_chains if c['grp'] == g])):
            improvement_stats(f"   {lab}", recs)
        # returns / minima of re-descents
        mins = sorted(c['min'] for c in rd_c if c['grp'] == g)
        if mins:
            print(f"   REDESC cycle minima (incl. returns to the same best): {' '.join(str(m) for m in mins)}")

    print("\n== equal-CPU view: P(min<=c) per CPU-hour, fresh F-chains vs RA1/RA2 chains (same group) ==")
    for g in groups:
        ff = [c for c in fresh_chains if c['grp'] == g]
        if not ff:
            continue
        Tf = sum(c['dur'] for c in ff) / 3600.0
        for ra in ('RA1', 'RA2'):
            rr = [c for c in ra_chains if c['grp'] == g and c['kind'] == f'{ra}-chain']
            if not rr:
                continue
            Tr = sum(c['dur'] for c in rr) / 3600.0
            parts = []
            for cth in (10, 12, 15):
                kf = sum(1 for c in ff if c['min'] <= cth)
                kr = sum(1 for c in rr if c['min'] <= cth)
                parts.append(f"<= {cth}: fresh {kf}/{len(ff)} ({kf / Tf:.2f}/h) vs {ra} {kr}/{len(rr)} ({kr / Tr:.2f}/h)")
            print(f"  {g:5s} " + " | ".join(parts))

    print("\n== (b) tail models on fresh minima (per group; all policies pooled) ==")
    model_out = {}
    for g in groups:
        pool = fresh[g]
        n = len(pool)
        if n == 0:
            continue
        mins = [r['min'] for r in pool]
        mean_h = sum(r['dur'] for r in pool) / n / 3600.0
        f15 = [r for r in pool if r['policy'] == 'F15']
        mean_f15 = (sum(r['dur'] for r in f15) / len(f15) / 3600.0) if f15 else float('nan')
        print(f"-- {g}: n={n} mean CPU-h per fresh descent={mean_h:.4f} (F15 only: {mean_f15:.4f} h, n={len(f15)})")
        cum = {c: sum(1 for m in mins if m <= c) / n for c in (7, 8, 9, 10, 12, 15, 18)}
        print("   empirical P(min<=c): " + " ".join(f"{c}:{v:.3f}" for c, v in cum.items()))
        pol_h = {}
        for pol in ('F15', 'F30', 'F60', 'RESTART', 'FROMBEST-first'):
            sub = [r for r in pool if r['policy'] == pol]
            if sub:
                pol_h[pol] = sum(r['dur'] for r in sub) / len(sub) / 3600.0
        print("   CPU-h per descent by policy: " + ", ".join(f"{k} {v:.4f} (n={sum(1 for r in pool if r['policy'] == k)})"
                                                         for k, v in pol_h.items()))
        # (i) literal log-linear CDF: least squares of ln P(min<=c) on c for c in 9..18 (empirical CDF points)
        pts = [(c, sum(1 for m in mins if m <= c) / n) for c in range(9, 19, 1) if sum(1 for m in mins if m <= c) > 0]
        pts = [(c, f) for c, f in pts if f > 0]
        if len(pts) >= 3:
            xm = sum(c for c, _ in pts) / len(pts)
            ym = sum(math.log(f) for _, f in pts) / len(pts)
            beta = sum((c - xm) * (math.log(f) - ym) for c, f in pts) / sum((c - xm) ** 2 for c, _ in pts)
            alpha = ym - beta * xm
            p0 = math.exp(alpha)
            model_out[(g, 'cdf_ls')] = p0
            print(f"   log-linear CDF, least squares c=9..18: slope={beta:.3f} per cost unit, P(min=0)=exp(a)={p0:.2e} "
                  f"E[CPU-h to first 0] by policy: " + ", ".join(f"{k} {v / p0:.0f}" for k, v in pol_h.items()))
        # (ii) negative binomial in K=cost//3 fitted to all minima (overdispersion phi = var/mean)
        ks_all = [m // 3 for m in mins]
        best_nb = None
        for mi in range(20, 121):
            mu = mi / 10.0
            for pi in range(10, 61):
                phi = pi / 10.0
                if phi <= 1.0:
                    continue
                r = mu / (phi - 1.0)
                p = 1.0 / phi
                ll = 0.0
                for k in ks_all:
                    ll += math.lgamma(k + r) - math.lgamma(k + 1) - math.lgamma(r) + r * math.log(p) + k * math.log(1 - p)
                if best_nb is None or ll > best_nb[0]:
                    best_nb = (ll, mu, phi, r, p)
        if best_nb is not None:
            _, mu, phi, r, p = best_nb
            pk0 = p ** r
            f0 = sum(1 for m in mins if m % 3 == 0) / n
            p0 = pk0 * f0
            model_out[(g, 'nb')] = p0
            print(f"   negative binomial in K (all minima): mean K={mu:.1f} dispersion={phi:.2f} P(K=0)={pk0:.2e} "
                  f"x P(F=0)~{f0:.2f} -> P(min=0)={p0:.2e}  E[CPU-h to first 0] by policy: "
                  + ", ".join(f"{k} {v / p0:.0f}" for k, v in pol_h.items()))
        for ct in (15, 18):
            xs = [m for m in mins if m <= ct]
            q, p0c = truncated_geometric_mle(xs, ct)
            p0 = (len(xs) / n) * p0c
            model_out[(g, f'loglin{ct}')] = p0
            print(f"   log-linear tail, cut {ct}: q={q:.3f} (x{1 / q:.3f} per cost unit) P(min=0)={p0:.2e} "
                  f"E[CPU-h to first 0] by policy: " + ", ".join(f"{k} {v / p0:.0f}" for k, v in pol_h.items()))
        for kt in (4, 5):
            ks = [m // 3 for m in mins if m // 3 <= kt]
            lam, pk0c = truncated_poisson_mle(ks, kt)
            pk0 = (len(ks) / n) * pk0c
            f0 = sum(1 for m in mins if m % 3 == 0) / n
            p0 = pk0 * f0
            model_out[(g, f'pois{kt}')] = p0
            print(f"   Poisson in orbits K=cost//3 (cut K<={kt}): lambda={lam:.2f} P(K=0)={pk0:.2e} x P(F=0)~{f0:.2f} "
                  f"-> P(min=0)={p0:.2e}  E[CPU-h to first 0] by policy: "
                  + ", ".join(f"{k} {v / p0:.0f}" for k, v in pol_h.items()))

    print("\n== (d) fraction of final costs not a multiple of 3 (uncovered alpha-fixed elements) ==")
    for g in groups:
        ms = [r['min'] for r in fresh[g]] + [c['min'] for c in use_chains if c['grp'] == g and c['kind'].startswith('RA')]
        if ms:
            k = sum(1 for m in ms if m % 3)
            print(f"   {g:5s} fresh+RA minima: {k}/{len(ms)} = {k / len(ms):.3f} not multiple of 3")
    allm = [r['min'] for g in groups for r in fresh[g]] + [c['min'] for c in use_chains if c['kind'].startswith('RA')]
    print(f"   all fresh+RA minima: {sum(1 for m in allm if m % 3)}/{len(allm)} = {sum(1 for m in allm if m % 3) / len(allm):.3f}")
    rb = [r for r in results if not r.get('last_progress')]
    print(f"   RESULT best values (finished runs): {sorted(r['best'] for r in rb)} -> not multiple of 3: "
          f"{sum(1 for r in rb if r['best'] % 3)}/{len(rb)}")
    lp = [r['best'] for r in results if r.get('last_progress')]
    print(f"   last global best of each log: {sorted(lp)}")


if __name__ == '__main__':
    main()
