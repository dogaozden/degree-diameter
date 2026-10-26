STATS_T = 0
W = int(os.environ.get('W', 6)); LEV = int(os.environ.get('LEV', 6)); TLB = float(os.environ.get('TLB', 300))
TMAX = int(os.environ.get('TMAX', 12))
T0b = time.time()
def ev_state(sg, nn):
    sig[:] = sg; nu[:] = nn; set_unmixed(nu)
t_root, parts_root = total(sig)
c_root = c_now()
beam = [(t_root, c_root, sig.copy(), nu.copy(), [])]
root_sig, root_nu = sig.copy(), nu.copy()
visited = {(sig.tobytes(), nu.tobytes())}
bestT, bestS = t_root, (sig.copy(), nu.copy(), parts_root, [])
print('beam root total %d c %d' % (t_root, c_root), flush=True)
found = None
for lev in range(LEV):
    children = []
    for (t, c, sg, nn, path) in beam:
        ev_state(sg, nn)
        for pr in bads():
            for mv in opts(pr):
                if mv[0] == 'F':
                    apply(mv); c2 = c_now(); t2 = c2 + (t - c)   # flips leave coverage and D1 unchanged
                    if c2 + (t - c) <= TMAX:
                        children.append((t2, c2, mv, None, None, path + [mv], 'F'))
                    apply(mv)
                else:
                    apply(mv); c2 = c_now(); t2 = total(sig)[0]; STATS['totals'] += 1
                    apply(mv)
                    if t2 <= TMAX:
                        children.append((t2, c2, mv, None, None, path + [mv], 'S'))
        # materialise child states lazily: store parent state + move, rebuild when selected
    # select
    children.sort(key=lambda x: (x[0], x[1]))
    newbeam = []; seen_now = set()
    for (t2, c2, mv, _a, _b, pth, kind) in children:
        # rebuild the child from its parent path: replay path from root
        ev_state(root_sig, root_nu)
        for m in pth: apply(m)
        key = (sig.tobytes(), nu.tobytes())
        if key in visited or key in seen_now: continue
        seen_now.add(key); visited.add(key)
        newbeam.append((t2, c2, sig.copy(), nu.copy(), pth))
        if len(newbeam) >= W: break
    if not newbeam: print('no children at level', lev, flush=True); break
    beam = newbeam
    for (t, c, sg, nn, pth) in beam:
        if t < bestT: bestT = t; bestS = (sg.copy(), nn.copy(), None, pth)
        if c == 0 and t == 0: found = (sg.copy(), nn.copy(), pth)
    print('level %d: beam totals %s  c %s  best %d  children %d  elapsed %.0fs' % (
        lev, [b[0] for b in beam], [b[1] for b in beam], bestT, len(children), time.time() - T0b), flush=True)
    if found or time.time() - T0b > TLB: break
if found:
    sg, nn, pth = found
    print('SUCCESS total 0 path', [fmt(m) for m in pth], flush=True)
    sig[:] = sg; nu[:] = nn; set_unmixed(nu); cur = 0
    out = OUTDIR + '/best_beam.lift2.sol'; write(sig); print('wrote', out, flush=True)
else:
    sg, nn, parts, pth = bestS
    out = OUTDIR + '/bestseen_beam.lift2.sol'
    write_state(sg, nn, out)
    print('best seen total', bestT, 'path', [fmt(m) for m in pth], 'written', out, flush=True)
