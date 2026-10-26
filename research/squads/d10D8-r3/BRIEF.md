# Shared brief for round 3 (read this first)

Goal: an EXPLICIT (algebraic, not annealed) construction of a bipartite graph of max degree q+3 and diameter 8 on
c·|H(q)| vertices from the split Cayley hexagon H(q), with c ≥ 5·⌊(q+5)/2⌋ (= 20, 20, 25, 30 for q = 3, 4, 5, 7).
The table's (10,8) record is exactly 30·|H(7)| = 1,176,480, so a rule that reaches c = 31 at q = 7 beats it, and
a rule that reproduces 5·⌊(q+5)/2⌋ for q = 3, 4, 5 is probably the table's own construction (useful too).

Known facts:
1. H(q): points P, lines L, |P| = |L| = (q⁶−1)/(q−1); incidence graph is (q+1)-regular, girth 12, diameter 6;
   point–line distances 1, 3, 5; same-type distances 0, 2, 4, 6. Between elements at distance < 6 the geodesic is
   unique; opposite elements (distance 6) are joined by q+1 geodesics.
2. Ten-level lemma (proved): B = H(q) + two arbitrary bijections σ1, σ2: P → L, lifted over Z10 with hexagon edges
   at level 0 and the matching edges p–σ1(p), p–σ2(p) raising the level by 1 and 4 (from the point), has diameter
   ≤ 8 for every σ1, σ2. Routes from a point p to a line y with ≤ 2 matching edges: 0 (p⇝y), +a (p→σ(p)⇝y),
   −a (p⇝σ(x)→x→y, x on y: q+1 choices of x!), a+b (p→σ_a(p)⇝σ_b⁻¹(y)→y), a−b, a≠b (p→σ_a(p)→σ_b⁻¹σ_a(p)⇝y).
   So with Z5 levels (shifts 1, 2) most levels have only 1–3 such walks, and the level −a_t ones have q+1.
3. With hexagon voltages in a group K on top of levels, each (source, target, level) needs walks of all K-values.
   Random voltages fail at q = 7 (about 130 uncovered sheets per source at c = 30); annealing works only at q ≤ 4.
4. Incident matchings (σ_t(p) ∋ p, i.e. perfect matchings of the incidence graph) give 2-step "digons" p→σ(p)→p
   with level ±a at every vertex: good for near pairs, but distance-5 pairs only get 5 levels that way.
5. Squad round 2 (research/squads/d10D8-r2/c3/): explicit index-product rules reach 16 levels at q = 4 (formula 20),
   i.e. they behave like random voltages.

Tools (cd /home/user/degree-diameter/research/d10D8/hex first): H(q) data hex/hex_q{2,3,4,5,7}.bin (format in hexgen2.c
header: int32 q, N, L, then L*(q+1) int32 point ids (the points of line l), then N*7 uint8 PG(6,q) coordinates of the
points). Checker: lift3 with IN=<solution file> ITERS=0 prints "fullcost F" and DIAMETER_OK when F = 0 (all sources).
Solution file format: lift2.c save(): line "q J m D cost", group spec line (e.g. "cyc 30" or "prod 6 5" = Z6×Z5 with
index x = x_6·5 + x_5, or "file path" for a multiplication table), J lines of σ_t (point index → line index), J lines
of matching voltages (per point, element indices), then one line of hexagon voltages per flag, line-major: entry
l*(q+1)+k is the voltage of the flag (k-th point of line l, l), direction point → line. Example builder:
research/squads/d10D8-r2/c3/build_rule.py. Command: `IN=<file> GROUP="<spec>" J=2 D=8 ITERS=0 timeout 120 nice -n 19 ./lift3 <q>`
(the GROUP env must match the file's group). Full check time: seconds at q ≤ 5, about a minute at q = 7.

CPU rules: the 4 cores run the lead's main searches. ONE process at a time, `timeout 120 nice -n 19`, q ≤ 5 except one
final q = 7 check of your best rule (allowed once, `timeout 600 nice -n 19`). Total CPU under ~10 minutes.
Do NOT commit; edit only your card folder; append ONE JSON line to research/squads/d10D8-r3/scoreboard.jsonl:
{"card": "r3-cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <c at the largest q tested,
divided by 5*floor((q+5)/2)>, "valid": true|false, "next": "<one line>"}; reply in ≤ 5 lines.
