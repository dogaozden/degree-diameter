# Independent rebuild of the (16,5) 32,768-vertex graph from its definition, in GAP:
# group elements from SmallGroup(64,43) (AsSSortedList), arithmetic in GAP's GF(4) (code 0,1,2,3 = 0, 1, Z(4), Z(4)^2).
# Controller H(G,S): (g,A) ~ (s g,B). Label a: (g,A) -> (s1 g,B), (h,B) -> (s2^-1 h,A). Label b: s3, s4.
# Lift: (c, x) ~ (sigma_t(c), A_t x + lam b_t), t in {a, b}, lam in GF(4). Writes an edge list for apsp.
G := SmallGroup(64, 43); el := AsSSortedList(G); S := el{[1, 2, 3, 30]};
code := [0*Z(4), Z(4)^0, Z(4), Z(4)^2];
digits := "3212100322223231102333002001231130110333";
d := List(digits, c -> code[IntChar(c) - 47]);
Aa := [d{[1..4]}, d{[5..8]}, d{[9..12]}, d{[13..16]}]; ba := d{[17..20]};
Ab := [d{[21..24]}, d{[25..28]}, d{[29..32]}, d{[33..36]}]; bb := d{[37..40]};
V := List(Tuples([0..3], 4), t -> List(t, i -> code[i+1]));   # lexicographic, same order as the python builder
vpos := function(v) return Position(V, v); end;
Sort(V);   # make Position fast via binary search on a sorted copy; keep an index map
order := List(Tuples([0..3], 4), t -> List(t, i -> code[i+1]));
idx := List(V, v -> Position(order, v));   # idx[i] = lexicographic index of V[i]
vid := function(v) return idx[PositionSorted(V, v)] - 1; end;
n := 64;
cv := function(side, g) return side * n + Position(el, g) - 1; end;   # controller vertex number
out := OutputTextFile("rebuild_gap.edges", false); SetPrintFormattingStatus(out, false);
WriteAll(out, Concatenation(String(2 * n * 256), "\n"));
cnt := 0;
for side in [0, 1] do
  for g in el do
    for t in [1, 2] do
      if t = 1 then A := Aa; b := ba; else A := Ab; b := bb; fi;
      if side = 0 then h := S[2*t - 1] * g; dside := 1; else h := S[2*t]^-1 * g; dside := 0; fi;
      c1 := cv(side, g); c2 := cv(dside, h);
      for x in order do
        Ax := A * x;   # A acts on column vectors: (A x)_i = sum_j A[i][j] x[j]
        for lam in code do
          y := Ax + lam * b;
          u := c1 * 256 + vid(x); w := c2 * 256 + vid(y);
          WriteAll(out, Concatenation(String(Minimum(u, w)), " ", String(Maximum(u, w)), "\n"));
          cnt := cnt + 1;
        od;
      od;
    od;
  od;
od;
CloseStream(out);
Print("edges written ", cnt, "\n");
QUIT;
