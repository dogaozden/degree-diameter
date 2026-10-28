# Card c7 (squad d5relax-r1): exact calibration at q = 5, no spread condition

Folder: research/squads/d5relax-r1/c7/. Code: calib.py (SAT encoding over x_p, PSp(4,q) symmetry split).

## Encoding (calib.py)
- every line: no three of its points in T (clauses -a -b -c);
- every point v, lines L1 != L2 through v, a in L1-v, b in L2-v: clause (-v -a -b);
- sum x >= K by pysat CardEnc.atleast (totalizer).
- Cases: A = {0, 1} in T (1 a collinear point of 0), all other neighbours of 0 and 1 out.
  B = 0 in T, no neighbour of 0 in T, p2 = smallest point not collinear with 0 in T.
- Symmetry: PSp(4,5) transitive on points, ordered collinear pairs, ordered non-collinear pairs,
  so every relaxed set of size >= 2 is equivalent to a set of case A or case B.

## Validation
- W(3), no spread condition: K=11 SAT in full/A/B (0.0 s); K=12 UNSAT in full (0.2 s), A (0.0 s), B (0.0 s).
  Matches the known maximum 11 for W(3) without the condition (with the spread condition it is 10).
- W(5) soundness: the 23-set of gqd5-r2/c8 (bb5_t23, valid with the spread condition, hence valid here) is
  accepted by the clause set (calib.py 5 0 check witness23.json: SATISFIED). A set with three points on a line
  is rejected (neg_three_on_line.json: VIOLATED). Clause count for W(5): 61620 relaxed clauses.

## Results (q = 5, no spread condition)

1. Case A, K = 24, CaDiCaL 1.9 (cadical195), totalizer: TIMEOUT at 900 s, no answer (runA24_cadical.txt, exit 124).
2. Case B, K = 24: NOT RUN (budget: the 900 s case A run plus validation already used most of the card's compute
   allowance, and a case B timeout would not decide anything without a case A answer).
3. Local search for 24 (rtabu, no spread option, 240 s, seed 1, start 23): best 23 (tabu24_s1.txt, valid).
4. Witness of size 23: best.txt (also witness23.json), score.py 5 best.txt -> size 23, pairs 6, valid true.

Verdict: 24 is NOT proved impossible here, and no 24-set was found. The exact question stays open for this card.
The largest size proved to exist at q = 5 is 23.

## Commands

    cd research/squads/d5relax-r1/c7
    python3 calib.py 3 11 full ; python3 calib.py 3 12 full      # W(3): SAT 11, UNSAT 12
    python3 calib.py 3 12 A ; python3 calib.py 3 12 B            # UNSAT, UNSAT
    python3 calib.py 5 0 check witness23.json                    # encoding accepts the 23-set
    python3 calib.py 5 0 check neg_three_on_line.json            # VIOLATED (sanity)
    timeout 900 nice -n 10 python3 calib.py 5 24 A cadical195 totalizer > runA24_cadical.txt   # timeout
    cd ../../../theorems/d5relax && timeout 300 nice -n 10 ./rtabu data/W5_adj.txt 240 1 <c7>/tabu24_s1.txt -k 23 -t 24
    python3 ../../../theorems/d5relax/score.py 5 best.txt        # size 23, valid

## Next (for a successor card)

- Case A and case B at K = 24 with a stronger encoding or a dedicated branch and bound (the c8 group B&B used the
  spread; a substitute partition is needed without it), and/or kissat404 (faster than CaDiCaL on the W(5) ovoid runs).
