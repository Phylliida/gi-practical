# Independent checks with GAP on GL(V)_ell acting on W. Read after group_M.g defines m, genW, genR.
glOrder:=function(k) local r,i; r:=1; for i in [0..k-1] do r:=r*(2^k-2^i); od; return r; end;;
A:=Group(genW);;
W:=[1..Length(Wlines)];;
nlines:=(2^m-1)*(2^(m-1)-1)/3;;
Print("m=",m," |W|=",Length(W)," transitive on W: ",IsTransitive(A,W),"\n");;
Print("|A|=",Size(A),"  |GL(V)_ell|=",glOrder(m)/nlines,"  faithful/equal: ",Size(A)=glOrder(m)/nlines,"\n");;
w0:=1;;
stab:=Stabilizer(A,w0);;
orbs:=Orbits(stab,Difference(W,[w0]));;
Print("suborbit lengths on W: ",SortedList(List(orbs,Length)),"\n");;
sizes:=[];;
for o in orbs do
  b:=Blocks(A,W,[w0,o[1]]);;
  AddSet(sizes,Length(b[1]));;
od;
Print("minimal block sizes containing w0 and another point (over all suborbit reps): ",sizes,"\n");;
# identify the unique nontrivial system with its quotient
nontriv:=First(List(orbs,o->Blocks(A,W,[w0,o[1]])),b->Length(b[1])>1 and Length(b)>1);;
if nontriv<>fail then
  acting:=Action(A,nontriv,OnSets);;
  k:=m-2;;
  Print("blocks: ",Length(nontriv)," of size ",Length(nontriv[1]),"; expected ",(2^k-1)*(2^(k-1)-1)/3,"\n");;
  Print("|P| = ",Size(acting),"; |GL(",k,",2)| = ",glOrder(k),"; primitive: ",IsPrimitive(acting,[1..Length(nontriv)]),"\n");;
fi;;
