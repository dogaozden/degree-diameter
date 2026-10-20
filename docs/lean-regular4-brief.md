# Lean brief: regular diameter-4 graphs (Problem 4 at D = 4)

research/p4/d4/REPORT.md ("Update ~01:15: regular versions"): every Cor. B1 copy graph can be made Δ-regular by adding a
biregular bipartite graph between the point copies and the line copies; adding edges never increases distances, and the
diameter stays 4. In Lean (master has GQST.gqst, GQST.isBipartiteDegDiam, the blowup graph):
1. Lemma: adding edges to a graph does not increase ediam (SimpleGraph ≤ monotonicity of edist), and keeps
   2-colourability if the new edges go between the two colour classes.
2. Theorem: for a GQ of order (s,t) with an exact weighted (Δ−s−1)-ovoid w and an exact (Δ−t−1)-cover m (sums equal on
   every line / point), there is a Δ-regular bipartite graph of diameter ≤ 4 on Fin (|P|+|L|+Σw+Σm) vertices. Construct
   the added biregular graph explicitly (e.g. cyclic matchings) and prove regularity.
3. Instance: the 5440 graph (Q(4,13) + 2-cover, Prop C) is 16-regular — via SingerC.corC1 if convenient, or record a
   kernel-checked regular graph for (16,4) from research/p4/d4/graphs/regular_c1_q13_n5440.json with the staged machinery.
Rules: `scripts/stop_check.sh` before each step; builds through `scripts/guarded.sh HOURS ...`; total limit 4 hours.
No `sorry`/`admit`/`axiom`/`native_decide`; only the three standard axioms. Branch `lean-regular4`. Report as usual.
