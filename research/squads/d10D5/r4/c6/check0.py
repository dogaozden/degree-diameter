import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import lns
for fn in sys.argv[1:]:
    S = lns.read_sol(fn)
    t = time.time()
    c, unc = lns.cover(S['F'], S['sig'], S['hubadj'], listing=True)
    print(fn, 'cost', c, unc[:5], 'k', len(S['F']), 'hg edges', int(S['hubadj'].sum()), '%.1fs' % (time.time()-t))
