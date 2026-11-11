# raise-d8b round 2 cards (16). Rules in HEADER.md. Each card: ONE rung = one cell, one ORBIT, one group, one
# 1400-s haar_big0 run (`nohup env ORBIT="..." THREADS=1 nice -n 10 $BIN/haar_big0 d 8 1400 SEED 8 a.sol fam p n > a.log 2>&1 &`).
# If it solves (a RESULT line with best=0 and a.sol written): check a.sol with haarcheck_gen, then run the "next" rung
# for the rest of your time box. If it does not solve, report the best cost and the evaluation count.

## d01 (17,8) "5 3 2" on sl 41 311 (mu 33.6); next psl 41 631 (mu 41.2)
## d02 (17,8) "5 3 2" on psl 89 61 (mu 35.3); next psl 61 191 (mu 39.6)
Round 1 (r1/c15) left this exact group at cost 1: first copy /home/user/degree-diameter/research/squads/raise_d8b/r1/c15/s_k5_psl89_61.sol.best
into your folder and start from it (START=<your copy>, a new SEED). Never write into r1/.
## d03 (17,8) orbits of order 7, "7 2 3" on sl 29 883 (mu 35.6); next psl 43 547 (mu 41.3)
Before the search, RANDORB=16 on sl 29 883 with "7 2 3" and on sl 29 881 with "5 3 2" (equal mu); report both
(min, median, median/k) in your scoreboard "idea" field.
## d04 (18,8) "5 3 3" on psl 181 11 (mu 51.0) (bold: the director solved mu 44.2 in 18,549 evaluations); next none
## d05 (18,8) "5 3 3" on sl 31 1091 (mu 47.8); next psl 181 11 (mu 51.0)
## d06 (18,8) orbits of order 7, "7 2 4" on psl 97 71 (mu 46.3); next psl 43 827 (mu 56.8)
## d07 (19,8) "5 3 4" on psl 131 41 (mu 35.9); next psl 59 451 (mu 38.5)
## d08 (19,8) "3 6 1" on psl 43 1159 (mu 35.5) (k = 3 control at the k = 5 frontier); next none
## d09 (19,8) "5 3 4" on psl 89 131 (mu 36.9); next psl 79 191 (mu 49.3)
## d10 (19,8) "5 3 4" on psl 59 451 (mu 38.5); next psl 79 191 (mu 49.3)
## d11 (20,8) "5 4 0" on sl 79 131 (mu 29.2); next psl 109 101 (mu 35.4)
## d12 (20,8) "5 4 0" on psl 61 571 (mu 30.7); next psl 59 641 (mu 39.0)
## d13 (20,8) "5 4 0" on psl 109 101 (mu 35.4); next psl 229 11 (mu 41.3)
## d14 (20,8) "5 4 0" on psl 509 1 (mu 40.2, n = 1); next psl 229 11 (mu 41.3)

## d15 Wildcard: (19,8) with k = 5 and a NON-abelian centralizer (haar_sym)
At (19,8) k = 5 needs 4 alpha-fixed letters (19 = 4 + 15), and with alpha = conjugation by an element of order 5 they
all lie in an abelian torus, which makes 6-cycles. Fix: G = PSL(2,41) x SL(2,5) x Z11 (haar_sym group spec
`prod psl 41 sl 5 11`, N = 34,440 * 120 * 11 = 45,460,800, 90,921,600 vertices, mu ~ 29) with alpha = conjugation by
(g, I) where g has projective order 5 in PSL(2,41) and I is the identity of SL(2,5), times z -> r z (r of order 5 mod 11).
Then the fixed elements are torus x SL(2,5) x {0}, which is non-abelian. haar_sym picks alpha itself; override it with
ALPHA=<index> (research/structured/README.md; read haar_sym.c to see how a prod element's index is formed and how
alpha is printed: "alpha: conj by prod[mat(..);mat(..)] (index N)"). Run ORBIT="5 3 4" with that alpha (RANDORB=16
first, against the automatic alpha), then search the better one for the rest of the box. haar_sym is slower
(~0.3 s/eval here); its solution file is checked with haarcheck_gen (header "prod psl 41 sl 5", see haarcheck_gen.c).
Report the RANDORB numbers either way.

## d16 Wildcard: an approach none of the other cards uses
Other cards this round: single high rungs of k = 5 ("5 3 2", "5 3 3", "5 4 0", "5 3 4") and k = 7 at all four D = 8
cells, k = 3 "3 6 1" at (19,8), and a product group with non-abelian centralizer. Round 1 also tried: k = 3 ladders,
k = 9, haar_sym products with the default alpha, shape tournaments, hole anatomy, and multi-Haar lifts of K_{2,2} over
SL(2,p) (r1/c16). Find something different that could raise a D = 8 cell at d = 17..20 (or a D = 7 cell: current
(17,7) 5,693,959, (18,7) 7,309,092, (19,7) 11,316,940, (20,7) 15,795,219, hexagon level graphs with hubs), test it at
small scale, and report numbers.
