# Spot check of memo section 7, Grassmann row: line-transitive subgroups below GL(m,2).
LinesOf := function(m)
  local V, vecs, lines, i, j, u, v, w, L;
  vecs := Filtered(Elements(GF(2)^m), v -> not IsZero(v));
  lines := [];
  for i in [1..Length(vecs)] do for j in [i+1..Length(vecs)] do
    u := vecs[i]; v := vecs[j]; w := u + v;
    if not Set([u,v,w]) in lines then Add(lines, Set([u,v,w])); fi;
  od; od;
  return [vecs, Set(lines)];
end;
Check := function(name, G, m)
  local dat, vecs, lines, act, H, orbs, meeting, n, pairs, o;
  dat := LinesOf(m); vecs := dat[1]; lines := dat[2];
  act := g -> PermList(List(lines, L -> Position(lines, Set(L, v -> v * g))));
  H := Group(List(GeneratorsOfGroup(G), act));
  n := Length(lines);
  orbs := Orbits(H, [1..n]);
  meeting := Filtered(Tuples([1..n], 2), p -> p[1] <> p[2] and Size(Intersection(lines[p[1]], lines[p[2]])) = 1);
  o := Orbits(H, meeting, OnTuples);
  Print(name, ": |G|=", Size(G), " lines=", n, " orbits on lines=", List(orbs, Length),
        " ordered meeting pairs=", Length(meeting), " orbit sizes=", List(o, Length), "\n");
end;
# A7 in GL(4,2): a maximal subgroup of index 8
G := GL(4,2);
for H in MaximalSubgroupClassReps(G) do
  if Size(H) = 2520 then Check("A7 < GL(4,2)", H, 4); fi;
od;
# GammaL(1,32) in GL(5,2)
F := GF(2^5); z := PrimitiveRoot(F);
B := Basis(F);
mat := x -> List(BasisVectors(B), b -> Coefficients(B, b * x));
frob := List(BasisVectors(B), b -> Coefficients(B, b^2));
Check("GammaL(1,32) < GL(5,2)", Group(mat(z) * One(GF(2)), frob * One(GF(2))), 5);
QUIT;
