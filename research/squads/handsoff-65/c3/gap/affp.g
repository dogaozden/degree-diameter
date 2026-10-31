# affine group Z_p : C_k with C_k = <x -> g x> (g of order k in Z_p^*), acting on p points
AffP := function(p, k)
  local r, g, t, m;
  r := PrimitiveRootMod(p);
  g := PowerMod(r, (p-1)/k, p);
  t := PermList(List([0..p-1], x -> ((x+1) mod p) + 1));
  m := PermList(List([0..p-1], x -> ((g*x) mod p) + 1));
  return Group(t, m);
end;
