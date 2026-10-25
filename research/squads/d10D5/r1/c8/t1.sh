cd /home/user/degree-diameter/research/squads/d10D5/r1/c8
timeout 900 nice -n 10 python3 -c "
import sys, random, time
sys.path.insert(0,'.')
from obst import Geo
geo = Geo()
# flaggreedy-style 5 flags from the SIGMA-free check: random non-conflicting flags
rng = random.Random(5)
t0=time.time()
flags=[]
cands=[(p,l) for p in range(geo.N) for l in geo.lof[p]] if hasattr(geo,'lof') else None
" ; echo ok
