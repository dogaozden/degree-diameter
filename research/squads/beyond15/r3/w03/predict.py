import re, json, math, os, glob
os.chdir('/home/user/degree-diameter/research/squads/beyond15/r3/w03')
rows = json.load(open('table.json'))
def solve(W, mu=3.0):
    n = W / 5.0
    for _ in range(200):
        n = W / max(math.log(n / mu), 0.5)
    return n
out = {}
for r in rows:
    nm = r['name']; V = r['V']
    for D in (15, 16):
        txt = open(f'out_{nm}_D{D}.txt').read()
        srcs = re.findall(r'src \d+ walks (\d+) minW (\d+) at v=\d+ sumW (\d+)', txt)
        tot = int(srcs[0][0])
        wavg = sum(int(s[2]) for s in srcs) / len(srcs) / V       # mean distinct per endpoint
        wmin = int(r[f'nmax{D}'])
        walks_pe = tot / V                                       # raw nonbacktracking walks per endpoint
        r[f'wavg{D}'] = wavg; r[f'walks_pe{D}'] = walks_pe
        r[f'pred_min{D}'] = solve(wmin); r[f'pred_avg{D}'] = solve(wavg); r[f'pred_raw{D}'] = solve(walks_pe)
    print(f"{nm:9s} V={V:3d} g={r['girth']:2d} | D15: Wmin={r['nmax15']:5d} Wavg={r['wavg15']:8.0f} walks/V={r['walks_pe15']:7.0f} r={r['ravg15']:.3f} "
          f"| D16: Wmin={r['nmax16']:5d} Wavg={r['wavg16']:8.0f} r={r['ravg16']:.3f}")
    print(f"{'':9s}          pred n (mu=3): D15 min={r['pred_min15']:7.0f} avg={r['pred_avg15']:7.0f} raw={r['pred_raw15']:7.0f} | D16 min={r['pred_min16']:7.0f} avg={r['pred_avg16']:7.0f} raw={r['pred_raw16']:7.0f}")
json.dump(rows, open('table2.json', 'w'), indent=1)
