# gsets.g (deep-37): enumerate G-sets on which a (3,7)-graph with n vertices could have G as a group of automorphisms,
# and write orbdfs group files.  Input variables (set before Read): G (a group), N (vertex count), OUTDIR (string),
# TAG (string), MAXSETS (int).  Conditions used:
#  * every element of prime order p >= 5 acts freely (cubic connected graphs: a fixed vertex of a p-element, p > 3,
#    has its neighbours fixed, so the element is trivial);  so stabilisers are {2,3}-groups;
#  * colour kernel K = G (colour-preserving) or an index-2 subgroup (then stabilisers lie in K, orbits split evenly);
#  * N/2 vertices per side.
# For each K (G itself and each index-2 subgroup up to conjugacy... normal anyway) and each multiset of conjugacy
# classes of admissible stabilisers whose orbit sizes fit, a file OUTDIR/TAG_k<K>_<j>.txt is written.
LoadPackage("smallgrp");
stabok := function(H) return ForAll(Set(Factors(Size(H))), p -> p <= 3); end;
writegset := function(fn, G, K, specs)  # specs: list of [H, colour]
  local pts, perms, off, sp, H, act, cos, nH, el, ims, colours, g, i, rt, P, x, c;
  # build combined action: for each orbit, right cosets of H
  colours := []; off := 0; perms := List(Elements(G), g -> []);
  el := Elements(G);
  for sp in specs do
    H := sp[1]; cos := RightCosets(G, H); nH := Length(cos);
    for i in [1..Length(el)] do
      ims := List(cos, c -> Position(cos, c * el[i]));   # OnRight
      Append(perms[i], List(ims, x -> x - 1 + off));
    od;
    for c in cos do
      if K = G then Add(colours, sp[2]); else
        rt := Representative(c);
        if rt in K then Add(colours, 0); else Add(colours, 1); fi;
      fi;
    od;
    off := off + nH;
  od;
  PrintTo(fn, off, " ", Length(el), "\n");
  for P in perms do AppendTo(fn, JoinStringsWithSeparator(List(P, String), " "), "\n"); od;
  AppendTo(fn, JoinStringsWithSeparator(List(colours, String), " "), "\n");
end;
dosets := function(G, N, OUTDIR, TAG, MAXSETS)
  local Ks, K, cls, adm, H, sizes, half, results, rec2, cnt, kk, combos, cc, specs, i, j, c, fn, side, nA, nB, desc;
  half := N / 2;
  Ks := [G];
  Append(Ks, Filtered(List(NormalSubgroups(G)), S -> Index(G, S) = 2));
  cnt := 0;
  for kk in [1..Length(Ks)] do
    K := Ks[kk];
    cls := List(ConjugacyClassesSubgroups(G), Representative);
    adm := Filtered(cls, H -> stabok(H) and IsSubgroup(K, H));
    if K = G then
      # monochromatic orbits: choose multisets for side A and side B independently, each summing to half
      sizes := List(adm, H -> Index(G, H));
      combos := RestrictedPartitions(half, Set(sizes));
      # expand partitions into multisets of subgroup classes (several classes may share a size)
      cc := [];
      for c in combos do
        rec2 := [[]];
        for i in Set(c) do
          j := Number(c, x -> x = i);
          rec2 := Concatenation(List(rec2, r -> List(UnorderedTuples(Filtered([1..Length(adm)], t -> sizes[t] = i), j), u -> Concatenation(r, u))));
        od;
        Append(cc, rec2);
      od;
      for i in cc do for j in cc do
        if cnt >= MAXSETS then break; fi;
        specs := Concatenation(List(i, t -> [adm[t], 0]), List(j, t -> [adm[t], 1]));
        cnt := cnt + 1;
        fn := Concatenation(OUTDIR, "/", TAG, "_k", String(kk), "_", String(cnt), ".txt");
        desc := Concatenation("A:", String(List(i, t -> Size(adm[t]))), " B:", String(List(j, t -> Size(adm[t]))));
        Print(fn, " ", desc, "\n");
        writegset(fn, G, K, specs);
      od; od;
    else
      sizes := List(adm, H -> Index(G, H));
      combos := RestrictedPartitions(N, Set(sizes));
      for c in combos do
        rec2 := [[]];
        for i in Set(c) do
          j := Number(c, x -> x = i);
          rec2 := Concatenation(List(rec2, r -> List(UnorderedTuples(Filtered([1..Length(adm)], t -> sizes[t] = i), j), u -> Concatenation(r, u))));
        od;
        for i in rec2 do
          if cnt >= MAXSETS then break; fi;
          specs := List(i, t -> [adm[t], 0]);
          cnt := cnt + 1;
          fn := Concatenation(OUTDIR, "/", TAG, "_k", String(kk), "_", String(cnt), ".txt");
          desc := Concatenation("rev stabs:", String(List(i, t -> Size(adm[t]))));
          Print(fn, " ", desc, "\n");
          writegset(fn, G, K, specs);
        od;
      od;
    fi;
  od;
  return cnt;
end;
