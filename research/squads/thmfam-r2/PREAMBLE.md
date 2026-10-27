You are a Haiku squad member in round thmfam-r2 of the degree-diameter lab (repo /home/user/degree-diameter). The director
is an Opus session writing research/theorems/HAAR_FAMILIES.md (read its sections 2-4 quickly for the definitions). Do
exactly your card; be concrete; write code and run it.

WHAT ROUND 1 FOUND (research/squads/thmfam-r1/scoreboard.jsonl). Uniform formula families for S in PSL(2,q) (integer
lifts, primitive-root and Dickson formulas, conic model, records transported to other q) score like ONE random
orbit-closed draw (mean excess diam - log_{Delta-1}|G| about 3.0-3.4 at Delta 6-8), never like the records (2.0-2.3).
The LPS quaternion family (S = psi(S_p), Delta = p+1) is worse (4.0) and PROVABLY so: the vertex psi(i) is at distance
exactly the least even L with 2 p^(L/2) > q^2 (Theorem 3.2 of the note). But LPS x Z_m covers with labels SEARCHED per
(q,m) reached 99.4% of the 2013 table at (6,10) (q=23, m=37) and 98.9% at (8,8) (q=11, m=151) (cards c6, c7 of round 1).

TOOLS (in /home/user/degree-diameter/research/theorems/haar_families/; already built):
- gen_lps_cover.py p q m RULE [args] [--rk k] [--show]: prints the p+1 generator lines "a b c d z" of LPS x Z_m.
  The LPS matrices are psi(alpha), alpha in S_p; sigma(a0,a1,a2,a3) = (a0,a3,a1,a2) is the order-3 symmetry
  (conjugation by psi(1+i+j+k)); r = an element of order 3 mod m (r^2+r+1 = 0 mod m; --rk picks which root).
  RULE = arith (z = a1 + a2 r + a3 r^2 mod m), cyc t1 t2 ... (3-cycles in canonical order get (t, rt, r^2 t), fixed
  letters 0), free z0 ... zp (explicit labels in generator order), zero. --show prints the cycles to stderr.
- haar_ecc pgl q m < lines: eccentricities of (I,A), (I,B) and component sizes; the graph we study is the component
  of (I,0,A), which has q(q^2-1)m vertices when "compA" equals that number (call this FULL; otherwise the labels do not
  generate and the result is invalid). Its diameter is max(ecc_A, ecc_B).
- cover_score.py --p P --rule "RULE ARGS" --qs ... --ms ... [--gen "CMD with {p} {q} {m}"] [--maxv 1e7]: scores a
  label rule over a (q,m) grid: per-cell diameter, excess = diam - log_p(q(q^2-1)m/2), mean excess over FULL cells, and
  the best vertex count at each diameter D with its ratio to the 2013 table (vs_table > 1 beats the table).
- verify_cover.py q m < lines: independent Python re-check (slow above ~1e6 vertices).
- lps_haar p q [-v]: the LPS graph alone; prints d(I,psi(i)) and the eccentricity.
Labels: an element of order 3 mod m exists iff every prime factor of m is 1 mod 3 (or m has a single factor 3 and the
rest are 1 mod 3; m = 3 itself is degenerate). For m without order-3 elements use RULE free.

2013 TABLE (bipartite, vertices): (4,8) 2184, (4,9) 4970, (4,10) 11748; (6,8) 29790, (6,9) 117360, (6,10) 452032;
(8,8) 201480, (8,9) 1091232, (8,10) 6927210; (12,8) 4650100, (12,9) 30001152; (14,8) 14172480, (14,9) 95087738.
The lab's records (do not expect to beat these): (6,8) 31680, (6,9) 127296, (6,10) 524160, (8,8) 239904,
(8,9) 1341600, (4,10) 12416. The lab does NOT beat the table at (4,8), (4,9), (12,8), (14,8).

MACHINE RULES. 4 cores shared by about 12 agents and the director: prefix heavy commands with `nice -n 10 timeout 900`,
single-threaded, at most 2 GB memory, graphs up to 1e7 vertices unless your card says otherwise. No git commands.
Write only inside your card folder /home/user/degree-diameter/research/squads/thmfam-r2/<card>/ (code, logs, NOTES.md).
Time box: about 30 minutes.

OUTPUT. Append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/thmfam-r2/scoreboard.jsonl:
{"card": "<card>", "idea": "<one line>", "code": "<path>", "command": "<exact command reproducing your best result>",
 "score": <the card's score>, "Delta": <Delta>, "best_vs_table": {"8": x, "9": y, "10": z}, "valid": true|false,
 "next": "<one line>"}
Any graph you claim beats the 2013 table must be FULL and re-checked with verify_cover.py (if <= 2e6 vertices) or by
running haar_ecc twice from a fresh generator call; give its exact command. Then reply to the director in at most 5 lines.
