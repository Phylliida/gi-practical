# Unordered-pair tower: overgroups of Stab_GL(U)({S1,S2}) in GL(U), k=5.
k:=5;;
pts:=List(Filtered(Tuples([0*Z(2),Z(2)^0],k),v->not IsZero(v)),v->v);;
G:=Action(GL(k,2),pts,OnRight);;
Print("GL(",k,",2) on points: order ",Size(G),"\n");;
idx:=v->Position(pts,v);;
S1:=[[1,0,0,0,0],[0,1,0,0,0],[1,1,0,0,0]];;
S2:=[[0,0,1,0,0],[0,0,0,1,0],[0,0,1,1,0]];;
ToF2:=function(v) return List(v,x->x*Z(2)^0); end;;
A1:=Set(List(S1,ToF2),idx);; A2:=Set(List(S2,ToF2),idx);;
T:=Stabilizer(G,Set([A1,A2]),OnSetsSets);;
Print("|Stab({S1,S2})| = ",Size(T),"  index ",Size(G)/Size(T),"\n");;
L:=IntermediateSubgroups(G,T);;
Print("intermediate subgroups strictly between T and G: ",Length(L.subgroups),"\n");;
Print("orders: ",List(L.subgroups,Size),"\n");;
Print("inclusions (0=T, last+1=G): ",L.inclusions,"\n");;
for S in L.subgroups do
  Print("order ",Size(S)," index ",Size(G)/Size(S),": orbits on points ",SortedList(List(Orbits(S,[1..31]),Length)),"\n");;
od;;
QUIT;;
