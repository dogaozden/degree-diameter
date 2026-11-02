LoadPackage("smallgrp");
# gsets169.g (deep-37 round 2, card d2): G-sets for a (3,7)-graph on 169 vertices with side A = 85 (colour 0),
# side B = 84 (colour 1); the degree-2 vertices form a set of size 3 inside A (a union of G-orbits, target degree 2),
# all other vertices target degree 3. Colour-preserving only (85 != 84). Stabilisers must be {2,3}-groups
# (prime order p >= 5 is impossible: 85 and 84 are not both divisible by p). Faithful actions only.
# Variables before Read: G, OUTDIR, TAG, MP (max orbits per side for A3 and B), MAXSETS (max files written).
# Writes OUTDIR/TAG_<i>.txt (orbdfs group file, n = 169) and OUTDIR/TAG_<i>.deg2 (degree-2 vertices, comma list).
# Prints "file  #orbits  description" per file. Files come in order of increasing total orbit count.

stabok := function(H) return ForAll(Set(Factors(Size(H))), p -> p <= 3); end;

# all multisets of class positions (nondecreasing) with index sum S and at most MP parts
msets := function(idx, S, MP)
  local res, rc;
  res := [];
  rc := function(start, rem, cur)
    local i;
    if rem = 0 then Add(res, ShallowCopy(cur)); return; fi;
    if Length(cur) >= MP then return; fi;
    for i in [start..Length(idx)] do
      if idx[i] <= rem then
        Add(cur, i);
        rc(i, rem - idx[i], cur);
        Remove(cur);
      fi;
    od;
  end;
  rc(1, S, []);
  return res;
end;

gsets169 := function(G, OUTDIR, TAG, MP, MAXSETS)
  local el, cls, adm, idx, dcos, dims, L2, L3, LB, combos, c, specs, perms, off, sp, t, cos,
        colours, targets, out, d2, fn, cnt, desc, P, x, y, p3;
  el := Elements(G);
  cls := List(ConjugacyClassesSubgroups(G), Representative);
  adm := Filtered(cls, H -> stabok(H));
  idx := List(adm, H -> Index(G, H));
  # per admissible class: right cosets, and for each element the images (positions) of the cosets
  dcos := List(adm, H -> RightCosets(G, H));
  dims := List([1..Length(adm)], t -> List(el, g -> List(dcos[t], cc -> Position(dcos[t], cc * g))));
  L2 := msets(idx, 3, 3);
  L3 := msets(idx, 82, MP);
  LB := msets(idx, 84, MP);
  Print("# ", StructureDescription(G), " |G|=", Size(G), " classes=", Length(adm), " index=", idx,
        " |L2|=", Length(L2), " |L3|=", Length(L3), " |LB|=", Length(LB), "\n");
  # lazily: by total number of orbits T = |c| + |x| + |p3| (fewest orbits first), x with exactly k parts on A, p3 on B
  byk := function(list) local r, z, k; r := List([1..MP], k -> []); for z in list do Add(r[Length(z)], z); od; return r; end;
  L3k := byk(L3); LBk := byk(LB);
  combos := [];
  for T in [3..3+2*MP] do
    for c in L2 do for k in [1..MP] do for kb in [1..MP] do
      if Length(c) + k + kb = T then
        for x in L3k[k] do for p3 in LBk[kb] do Add(combos, [T, c, x, p3]); od; od;
      fi;
    od; od; od;
    if Length(combos) >= MAXSETS then break; fi;
  od;
  cnt := 0;
  for c in combos do
    if cnt < MAXSETS then
      specs := Concatenation(List(c[2], t -> [t, 0, 2]), List(c[3], t -> [t, 0, 3]), List(c[4], t -> [t, 1, 3]));
      perms := List(el, g -> []); colours := []; targets := []; off := 0;
      for sp in specs do
        t := sp[1];
        for x in [1..Length(el)] do
          Append(perms[x], List(dims[t][x], y -> y - 1 + off));
        od;
        for x in dcos[t] do Add(colours, sp[2]); Add(targets, sp[3]); od;
        off := off + Length(dcos[t]);
      od;
      if off <> 169 then Error("size ", off); fi;
      if Length(Set(perms)) = Length(el) then
        cnt := cnt + 1;
        fn := Concatenation(OUTDIR, "/", TAG, "_", String(cnt), ".txt");
        out := OutputTextFile(fn, false); SetPrintFormattingStatus(out, false);
        PrintTo(out, off, " ", Length(el), "\n");
        for x in perms do AppendTo(out, JoinStringsWithSeparator(List(x, String), " "), "\n"); od;
        AppendTo(out, JoinStringsWithSeparator(List(colours, String), " "), "\n");
        CloseStream(out);
        d2 := Filtered([0..off-1], v -> targets[v+1] = 2);
        out := OutputTextFile(Concatenation(OUTDIR, "/", TAG, "_", String(cnt), ".deg2"), false);
        PrintTo(out, JoinStringsWithSeparator(List(d2, String), ","), "\n");
        CloseStream(out);
        desc := Concatenation("A2:", String(List(c[2], t -> Index(G, adm[t]))), " A3:", String(List(c[3], t -> Index(G, adm[t]))),
                              " B:", String(List(c[4], t -> Index(G, adm[t]))));
        Print(fn, " ", String(c[1]), " ", desc, "\n");
      fi;
    fi;
  od;
  return cnt;
end;
