# w49 Lemma B': block systems of GL(d,2)xGL(e,2) on injective d-by-e matrices (columns are vectors of F_2^d)
BlockCheck:=function(d,e)
  local F,vecs,W,gl1,gl2,act,gens,G,bl,sizes;
  F:=GF(2);
  W:=Filtered(Tuples(Elements(F^d){[2..2^d]},e),t->Rank(t)=e);
  W:=Set(W);
  Print("|W|=",Length(W),"\n");
  gl1:=GeneratorsOfGroup(GL(d,2));
  gl2:=GeneratorsOfGroup(GL(e,2));
  # left action: columns c -> c*g^T ; here tuples are row-lists of column vectors of F^d
  gens:=[];
  for act in gl1 do
    Add(gens,PermList(List(W,t->Position(W,List(t,c->c*act)))));
  od;
  for act in gl2 do
    # right action on the tuple (c_1,..,c_e): new c_i = sum_j act[i][j] c_j
    Add(gens,PermList(List(W,t->Position(W,List([1..e],i->Sum([1..e],j->act[i][j]*t[j]))))));
  od;
  G:=Group(gens);
  Print("|G|=",Size(G),"\n");
  bl:=AllBlocks(G);
  sizes:=List(bl,Length);
  Print("nontrivial block sizes containing point 1: ",sizes,"\n");
  return sizes;
end;
BlockCheck(4,3);
QUIT;
