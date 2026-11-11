# raise-d8b round 5 cards (16). Rules in HEADER.md. Command shape:
#   cp <STATE> mystate && nohup env ORBIT="k m f" START=mystate THREADS=1 nice -n 10 $BIN/haar_big0 d 8 1400 SEED 8 a.sol fam p n > a.log 2>&1 &
# (haar_big0w with ORBW=5 where the card says so; "fresh" = no START). Poll with sleep 100. Check any a.sol.

## g01 (17,8) "7 2 3" sl 281 1 (mu 55.2), haar_big0, fresh, SEED 1
## g02 (17,8) "7 2 3" sl 281 1 (mu 55.2), haar_big0, fresh, SEED 2
## g03 (17,8) "7 2 3" sl 43 281 (mu 60.2), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r3/e03/a.sol.best, SEED 2
## g04 (17,8) "5 3 2" psl 31 1481 (mu 50.2), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r4/f13/a.sol.best, SEED 3
## g05 (18,8) "7 2 4" psl 29 2689 (mu 54.2), haar_big0, fresh, SEED 1
## g06 (18,8) "7 2 4" psl 41 953 (mu 55.9), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r4/f10/a.sol.best, SEED 2
## g07 (18,8) "7 2 4" psl 41 953 (mu 55.9), haar_big0, fresh, SEED 3
## g08 (19,8) "5 3 4" psl 79 191 (mu 49.3), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r4/f08/a.sol.best, SEED 3
## g09 (19,8) "5 3 4" psl 41 1361 (mu 46.2), haar_big0, fresh, SEED 1
## g10 (19,8) "5 3 4" psl 41 1361 (mu 46.2), haar_big0, fresh, SEED 2
## g11 (20,8) "5 4 0" psl 59 641 (mu 39.0), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r4/f04/a.sol.best.orb, SEED 2
## g12 (20,8) "5 4 0" psl 41 1901 (mu 36.1), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r4/f01/a.sol.best.orb, SEED 3
## g13 (20,8) "5 4 0" psl 79 271 (mu 49.0), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r4/f03/a.sol.best.orb, SEED 3
## g14 (20,8) "5 4 0" psl 41 1931 (mu 45.8), haar_big0w ORBW=5, fresh, SEED 2
(If a named STATE file does not exist, copy the newest *.best or *.orb file of that folder; if none, run fresh.)

## g15 Fixed-hole repair for "5 4 0" at D = 8 (coding card; small test only)
The (20,8) "5 4 0" near misses end with 1-2 alpha-fixed holes x (r3/e13). haar_big0's FIXF option (D = 10 only, see the
FIXF comment block in /home/user/degree-diameter/research/frontier/raise_d8/haar_big0w.c) screens each candidate on the
fixed elements by meet in the middle. Write the D = 8 analogue in a copy of haar_big0w.c in your folder: for D = 8 the
B side reached from (e,A) within 7 steps is Y_7 = S S^-1 S Y_4-type words; derive the split (e.g. x in Y_7 iff
v x in Y_3 for some v in (S S^-1)^2, so build Y_3 = S S^-1 S once per candidate and test the fixed elements, one v per
alpha-orbit). Check on a small group (e.g. psl 13 7, d = 6..8, D = 8) that your screen's count of uncovered
fixed elements equals the full evaluation's count (EVAL=... UNCPRINT=1) on 20 random S. Report timings and whether
it works; do not run big searches.

## g16 Wildcard (D = 8): an approach none of the other cards uses
Other cards: k = 7 / k = 5 orbit searches and near-miss continuations, ORBW, a fixed-hole screen. Ruled out so far:
k = 3 ladders (slower), k = 4, k = 9, single orbits of 11, k = 7 with f >= 5, "5 3 5", product groups, alpha with a
non-abelian centralizer, multi-Haar lifts, cyclic Haar graphs, PGL (r4/f16 did not finish: PGL(2,281) for (17,8) with
"5 3 2" in haar_sym, 2N = 44,375,520, is still untested; you may take that). Report numbers.
