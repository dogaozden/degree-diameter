# c4: G-sets with few orbits first (same admissibility rules as src/gsets.g; reuses its writegset).
# Inputs before Read: G, N, OUTDIR, TAG, MAXR (max orbits per side / total for rev), CAP.
Read("src/gsets.g");
stabok2 := function(H) return ForAll(Set(Factors(Size(H))), p -> p <= 3); end;
# all nondecreasing multisets of class indices (in cls) with orbit sizes summing to tot, length <= maxr
multisets := function(cls, sizes, tot, maxr)
  local out, mrec;
  out := [];
  mrec := function(start, rem, cur)
    local i;
    if rem = 0 then Add(out, ShallowCopy(cur)); return; fi;
    if Length(cur) >= maxr then return; fi;
    for i in [start..Length(cls)] do
      if sizes[i] <= rem then
        Add(cur, i); mrec(i, rem - sizes[i], cur); Remove(cur);
      fi;
    od;
  end;
  mrec(1, tot, []);
  return out;
end;
dofew := function(G, N, OUTDIR, TAG, MAXR, CAP)
  local Ks, K, kk, cls, adm, sizes, half, sides, pairs, cnt, sA, sB, specs, fn, desc, i, j, ord, rows, out, cnt2;
  half := N / 2; cnt := 0;
  Ks := [G]; Append(Ks, Filtered(List(NormalSubgroups(G)), S -> Index(G, S) = 2));
  out := OutputTextFile(Concatenation(OUTDIR, "/", TAG, "_list.txt"), false);
  SetPrintFormattingStatus(out, false);
  rows := [];
  for kk in [1..Length(Ks)] do
    K := Ks[kk];
    cls := Filtered(List(ConjugacyClassesSubgroups(G), Representative), H -> stabok2(H) and IsSubgroup(K, H));
    sizes := List(cls, H -> Index(G, H));
    if K = G then
      sides := multisets(cls, sizes, half, MAXR);
      # index by orbit count, combine pairs with smallest total count first
      for i in [1..Length(sides)] do
        sides[i] := [Length(sides[i]), sides[i]];
      od;
      Sort(sides, function(a, b) return a[1] < b[1]; end);
      sides := List(sides, s -> s[2]);
      for i in [1..Length(sides)] do for j in [i..Length(sides)] do
        if Length(sides[i]) + Length(sides[j]) > 2 * MAXR then continue; fi;
        Add(rows, [Length(sides[i]) + Length(sides[j]), kk, sides[i], sides[j]]);
      od; od;
    else
      sides := multisets(cls, sizes, N, MAXR + 2);
      for i in [1..Length(sides)] do Add(rows, [Length(sides[i]), kk, sides[i], []]); od;
    fi;
  od;
  Sort(rows, function(a, b) return a[1] < b[1]; end);
  # Sort is stable-ish; keep only the first CAP
  for i in [1..Minimum(CAP, Length(rows))] do
    K := Ks[rows[i][2]];
    cls := Filtered(List(ConjugacyClassesSubgroups(G), Representative), H -> stabok2(H) and IsSubgroup(K, H));
    if rows[i][4] = [] then
      specs := List(rows[i][3], t -> [cls[t], 0]);
      desc := Concatenation("rev orbits:", String(List(rows[i][3], t -> Index(G, cls[t]))));
    else
      specs := Concatenation(List(rows[i][3], t -> [cls[t], 0]), List(rows[i][4], t -> [cls[t], 1]));
      desc := Concatenation("A:", String(List(rows[i][3], t -> Index(G, cls[t]))), " B:", String(List(rows[i][4], t -> Index(G, cls[t]))));
    fi;
    fn := Concatenation(OUTDIR, "/", TAG, "_", String(i), ".txt");
    writegset(fn, G, K, specs);
    AppendTo(out, fn, " ", desc, "\n");
  od;
  CloseStream(out);
  return Minimum(CAP, Length(rows));
end;
