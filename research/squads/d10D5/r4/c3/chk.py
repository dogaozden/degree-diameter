import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/d10D5/r4'); import lns
S = lns.read_sol('k7.sol')
F = S['F']; sig = S['sig']
print('F', F, 'lines', [int(sig[p]) for p in F])
for p,l in [(291,47),(172,301)]:
    print('point',p,'line',l,'on?', bool(lns.PM is not None and (lns.INC[p,l])), 'sig(p)=',int(sig[p]), 'p freed?', p in F, 'sinv(l)=', int(list(sig).index(l)), 'l freed line?', l in [int(sig[x]) for x in F])
print('cover k7', lns.cover(F, sig, S['hubadj']))
print('hubadj', S['hubadj'].sum())
