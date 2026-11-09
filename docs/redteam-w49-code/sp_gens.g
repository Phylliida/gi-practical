# prints generators of Sp(d,2) as lists of integer row-masks (bit j of row i = entry (i,j))
for d in [2,4,6,8] do
  G := Sp(d,2);
  Print("d ", d, " ", Length(GeneratorsOfGroup(G)), "\n");
  for g in GeneratorsOfGroup(G) do
    for i in [1..d] do
      Print(Sum([1..d], j -> Int(g[i][j]) * 2^(j-1)), " ");
    od;
    Print("\n");
  od;
od;
QUIT;
