import sys, os, time
R4 = '/home/user/degree-diameter/research/squads/d10D5/r4'
sys.argv = ['lns3.py', '../r5/S5.sol', '../r5/S5_c0.lift2.sol', '1 6 5', '/dev/null']
os.environ['SECS'] = '0'
os.chdir(R4)
sys.path.insert(0, R4)
G = {'__name__': '__lns3__'}
src = open(R4 + '/lns3.py').read().split("best = cur; t0 = time.time()")[0]
t0 = time.time()
exec(compile(src, 'lns3_top', 'exec'), G)
print('loaded in %.1fs' % (time.time() - t0), G['cur'], G['parts'], flush=True)
