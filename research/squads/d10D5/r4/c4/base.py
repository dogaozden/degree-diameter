import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4'); import lns
for fn in sys.argv[1:]:
    S = lns.read_sol(fn)
    c, unc = lns.cover(S['F'], S['sig'], S['hubadj'], listing=True)
    print(fn, 'cover', c, 'holes', unc[:6], 'hubedges', int(S['hubadj'].sum()))
