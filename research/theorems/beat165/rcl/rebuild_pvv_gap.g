# Independent rebuild, in GAP, of a route-chart lift with per-base-vertex charts (the graphs built by buildlift_pvv.py).
# Set before reading: GN, GID (the group SmallGroup(GN, GID), elements in AsSSortedList order), K, PA, PB, FA, FB
# (0-based lists of length 2K: base permutations and voltage indices), CHARTS (2K strings "A16digits:b4digits"
# in the order v0 a, v0 b, v1 a, ...), OUTFILE.
# Controller vertex (v, g) -> v*m + (index of g); sigma_t(v, g) = (P_t[v], el[F_t[v]] * g).
# Lift: (c, x) ~ (sigma_t(c), A_{v,t} x + lam b_{v,t}), t in {a, b}, lam in GF(4); GF(4) codes 0,1,2,3 = 0, 1, Z(4), Z(4)^2.
# Lift vertex (c, x) -> c*256 + x1 + 4 x2 + 16 x3 + 64 x4 (codes). Writes one line per edge (duplicates not removed).
G := SmallGroup(GN, GID); el := AsSSortedList(G); m := Size(el);
code := [0*Z(4), Z(4)^0, Z(4), Z(4)^2];
num := e -> Position(code, e) - 1;
parse := function(s)
  local d;
  d := List(Filtered(s, c -> c <> ':'), c -> code[IntChar(c) - 47]);
  return [[d{[1..4]}, d{[5..8]}, d{[9..12]}, d{[13..16]}], d{[17..20]}];
end;
CH := List(CHARTS, parse);
VX := List(Tuples([0..3], 4), t -> List(t, i -> code[i+1]));
xid := x -> num(x[1]) + 4*num(x[2]) + 16*num(x[3]) + 64*num(x[4]);
out := OutputTextFile(OUTFILE, false); SetPrintFormattingStatus(out, false);
WriteAll(out, Concatenation(String(2 * K * m * 256), "\n"));
cnt := 0;
for v in [0 .. 2*K - 1] do
  for gi in [1 .. m] do
    for t in [1, 2] do
      if t = 1 then P := PA; F := FA; else P := PB; F := FB; fi;
      A := CH[2*v + t][1]; b := CH[2*v + t][2];
      c1 := v * m + gi - 1;
      c2 := P[v+1] * m + Position(el, el[F[v+1] + 1] * el[gi]) - 1;
      for x in VX do
        Ax := A * x;   # (A x)_i = sum_j A[i][j] x_j
        for lam in code do
          u := c1 * 256 + xid(x); w := c2 * 256 + xid(Ax + lam * b);
          WriteAll(out, Concatenation(String(Minimum(u, w)), " ", String(Maximum(u, w)), "\n"));
          cnt := cnt + 1;
        od;
      od;
    od;
  od;
od;
CloseStream(out);
Print("edge lines written ", cnt, "\n");
