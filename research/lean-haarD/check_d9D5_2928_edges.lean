import BipartiteDD.Haar.D9D5C61C24.Cert

/- Edge check for the (9,5) record on 2928 vertices (research/lean-haarD/STATUS-d95-2928.md).
   Prints the edges (enc g, 1464 + enc (s * g)) computed from the Lean definitions sS, enc, grpOf and the Group product.
   Compare with the edge file after sorting (run from lean/):
     lake env lean ../research/lean-haarD/check_d9D5_2928_edges.lean | head -n -1 | sort | cmp - <(tail -n +2 ../research/selfdual-d5/records/d9D5_n2928_haar_c61c24.edges | sort)
   The last line of the output is the edge count (13176). -/
open BipartiteDD.Haar.D9D5C61C24

/-- The edges `(enc g, 1464 + enc (s * g))`, `(g, A) ~ (s g, B)`, from the Lean definitions of `Grp`, `sS`, `enc`. -/
def leanEdges : List (ℕ × ℕ) :=
  (List.range 1464).flatMap fun n => (List.finRange 9).map fun k =>
    (enc (grpOf n), 1464 + enc (sS k * grpOf n))

#eval IO.println (String.intercalate "\n" (leanEdges.map fun p => s!"{p.1} {p.2}"))
#eval leanEdges.length
