import BipartiteDD.Haar.D7D5C41C16.Cert

/- Edge check for the (7,5) record on 1312 vertices (research/lean-haarD/STATUS-d75-1312.md).
   Prints the edges (enc g, 656 + enc (s * g)) computed from the Lean definitions sS, enc, grpOf and the Group product.
   Compare with the edge file after sorting (run from lean/):
     lake env lean ../research/lean-haarD/check_d7D5_1312_edges.lean | head -n -1 | sort | cmp - <(tail -n +2 ../research/d75-raise/records/d7D5_n1312_haar_c41c16.edges | sort)
   The last line of the output is the edge count (4592). -/
open BipartiteDD.Haar.D7D5C41C16

/-- The edges `(enc g, 656 + enc (s * g))`, `(g, A) ~ (s g, B)`, from the Lean definitions of `Grp`, `sS`, `enc`. -/
def leanEdges : List (ℕ × ℕ) :=
  (List.range 656).flatMap fun n => (List.finRange 7).map fun k =>
    (enc (grpOf n), 656 + enc (sS k * grpOf n))

#eval IO.println (String.intercalate "\n" (leanEdges.map fun p => s!"{p.1} {p.2}"))
#eval leanEdges.length
