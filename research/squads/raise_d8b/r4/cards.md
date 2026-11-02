# raise-d8b round 4 cards (16). Rules in HEADER.md. Command shape:
#   cp <STATE> mystate && nohup env ORBIT="k m f" START=mystate THREADS=1 nice -n 10 $BIN/haar_big0 d 8 1400 2 8 a.sol fam p n > a.log 2>&1 &
# (haar_big0w and ORBW=5 where the card says so; without a STATE, drop START and use SEED 1). Poll with sleep 100.
S=/home/user/degree-diameter/research/squads/raise_d8b

## f01 (20,8) "5 4 0" psl 41 1901 (mu 36.1), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r1/c10/b.sol.best.orb
## f02 (20,8) "5 4 0" psl 229 11 (mu 41.3), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r3/e09/a.sol.best.orb
## f03 (20,8) "5 4 0" psl 79 271 (mu 49.0), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r3/e10/a.sol.best.orb
## f04 (20,8) "5 4 0" psl 59 641 (mu 39.0), haar_big0w ORBW=5, no state (fresh, SEED 1)
## f05 (20,8) "5 4 0" psl 89 191 (mu 55.1), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r3/e11/a.sol.best.orb
## f06 (19,8) "5 3 4" psl 89 131 (mu 36.9), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r2/d09/a.sol.best (cost 5 = one orbit)
## f07 (19,8) "5 3 4" psl 59 451 (mu 38.5), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r2/d10/a.sol.best (cost 5)
## f08 (19,8) "5 3 4" psl 79 191 (mu 49.3), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r3/e06/a.sol.best (cost 10)
## f09 (19,8) "5 3 4" sl 71 131 (mu 46.3), haar_big0, no state (fresh, SEED 1)
## f10 (18,8) "7 2 4" psl 41 953 (mu 55.9), haar_big0, no state (fresh, SEED 1)
## f11 (18,8) "7 2 4" psl 43 827 (mu 56.8), haar_big0, no state (fresh, SEED 1)
## f12 (18,8) "5 3 3" psl 181 11 (mu 51.0), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r3/e04/a.sol.best (cost 13)
## f13 (17,8) "5 3 2" psl 31 1481 (mu 50.2), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r3/e02/a.sol.best (cost 10)
## f14 (17,8) "5 3 2" sl 89 31 (mu 44.5), haar_big0, no state (fresh, SEED 1); RANDORB=16 first against "7 2 3" on
psl 43 547 (mu 41.3) and search whichever has the lower median/k (report both).

## f15 Analysis: how many evaluations does a solve cost, as a function of mu/k? (light CPU, no searches)
Collect every haar_big0/haar_big0w log of this job: /home/user/degree-diameter/research/squads/raise_d8b/r*/*/*.log and
/home/user/degree-diameter/research/frontier/raise_d8/runs/*.log (skip RANDORB-only logs). For each run: cell d, group, k,
m, f, mu (from the header line "mu=..."), solved or not (RESULT ... best=0), evaluations at the end (or at the solve),
best cost, start state or fresh. Write runs.tsv. Then fit, over the solved runs, log(evals) ~ a + b * mu / k (and try
mu/k + c * f), and tabulate unsolved runs by mu/k. Report the fit, its spread, and the mu/k beyond which nothing solved
within ~1,400 s at ~0.2 core. Python only; write fit.txt in your folder.

## f16 Wildcard (D = 8): an approach none of the other cards uses
Other cards: k = 5 / k = 7 orbit searches with near-miss continuation and ORBW weighting of fixed holes, and a fit of
search cost against mu/k. Earlier rounds ruled out: k = 3 ladders (slower), k = 9, single orbits of 11, k = 7 with f = 6,
"5 3 5" at (20,8) (screens 3-8x worse than "5 4 0"), product groups (haar_sym), an alpha with non-abelian centralizer
(too many fixed points), multi-Haar lifts, cyclic Haar graphs. Find something different that could raise a D = 8 value
at d = 17..20, test it at small scale, report numbers.
