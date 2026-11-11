# raise-d8b round 6 cards (16), the last round. Rules in HEADER.md. Command shape:
#   cp <STATE> mystate && nohup env ORBIT="k m f" START=mystate THREADS=1 nice -n 10 $BIN/haar_big0 d 8 1400 SEED 8 a.sol fam p n > a.log 2>&1 &
# (haar_big0w with ORBW=5 where the card says so; "fresh" = no START). Poll with sleep 100. Check any a.sol.

## h01 (17,8) "5 3 2" psl 31 1481 (mu 50.2), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r5/g04/mystate, SEED 4
## h02 (17,8) "7 2 3" sl 43 281 (mu 60.2), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r5/g03/a.sol.best, SEED 3
## h03 (17,8) "5 3 2" psl 29 1801 (mu 47.0), haar_big0w ORBW=5, fresh, SEED 5
## h04 (18,8) "7 2 4" psl 41 953 (mu 55.9), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r5/g06/mystate, SEED 4
## h05 (18,8) "5 3 3" sl 31 1091 (mu 47.8), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r2/d05/a.sol.best, SEED 3
## h06 (18,8) "5 3 3" psl 181 11 (mu 51.0), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r4/f12/a.sol.best, SEED 3
## h07 (19,8) "5 3 4" psl 79 191 (mu 49.3), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r5/g08/mystate, SEED 4
## h08 (19,8) "5 3 4" psl 41 1361 (mu 46.2), haar_big0, STATE /home/user/degree-diameter/research/squads/raise_d8b/r5/g09/a.sol.best, SEED 3
## h09 (19,8) "5 3 4" psl 79 191 (mu 49.3), haar_big0, fresh, SEED 6
## h10 (20,8) "5 4 0" psl 29 5431 (mu 42.3), haar_big0w ORBW=5, fresh, SEED 1
## h11 (20,8) "5 4 0" sl 41 961 (mu 42.7), haar_big0w ORBW=5, fresh, SEED 1
## h12 (20,8) "5 4 0" psl 41 1931 (mu 45.8), haar_big0w ORBW=5, STATE /home/user/degree-diameter/research/squads/raise_d8b/r5/g14/a.sol.best.orb, SEED 3
## h13 (20,8) "5 4 0" psl 31 4451 (mu 43.1), haar_big0w ORBW=5, fresh, SEED 1
## h14 (20,8) "5 4 0" psl 29 5441 (mu 43.5), haar_big0w ORBW=5, fresh, SEED 1
(If a named STATE file does not exist, copy the newest *.best, *.orb or mystate file of that folder; if none, run fresh.)

## h15 Make the D = 8 fixed-hole screen fast (coding card; small tests only)
r5/g15 wrote /home/user/degree-diameter/research/squads/raise_d8b/r5/g15/haar_big0w8.c: FIXF=1 at D = 8 (x in Y_7 iff v x
in Y_3 for some v in (S S^-1)^2, one v per alpha-orbit), checked against full evaluations on 100 random S, but 0.18-0.28 s
per candidate at d = 20 because it builds the d^4 list of v each time. Copy it into your folder and make the screen cheap:
e.g. when one slot changes, only words that use the new letters are new, or build Y_3 once and test each fixed x by
scanning (S S^-1)^2 x lazily with early exit. Re-check equality against full evaluations on 50 random S (psl 13 7 and
psl 29 7) and report the new time per candidate at d = 17..20 (use psl 73 1 or similar small groups). No big searches.

## h16 Wildcard (D = 8): an approach none of the other cards uses
Other cards: continuations and fresh k = 5 / k = 7 runs, ORBW, a fixed-hole screen. Ruled out so far: k = 3 ladders,
k = 4, k = 9, single orbits of 11, k = 7 with f >= 5, "5 3 5", product groups, alpha with a non-abelian centralizer,
multi-Haar lifts, cyclic Haar graphs, PGL(2,281) in haar_sym (setup too slow here twice). Report numbers.
