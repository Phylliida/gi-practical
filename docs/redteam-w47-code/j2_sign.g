# J_2(m,2) with Y={ell}: permitted group = even-product-sign subgroup. Read after group_M.g.
A:=Group(genW);;
hom:=GroupHomomorphismByImages(A,Group(genR),genW,genR);;
eps:=List([1..Length(genW)],i->SignPerm(genW[i])*SignPerm(genR[i]));;
Print("m=",m," signs of GL(V)_ell generators (W*R): ",eps,"\n");;
Wpts:=[1..Length(Wlines)];;
L1:=Filtered(Elements(Group(())),x->false);;
# kernel of eps: compute via the homomorphism to C2 on A, using lifted sign on W and R
signW:=GroupHomomorphismByFunction(A,Group((1,2)),function(x) if SignPerm(x)=1 then return (); else return (1,2); fi; end);;
signR:=GroupHomomorphismByFunction(A,Group((1,2)),function(x) if SignPerm(Image(hom,x))=1 then return (); else return (1,2); fi; end);;
mix:=GroupHomomorphismByFunction(A,Group((1,2)),function(x) return Image(signW,x)*Image(signR,x); end);;
Lp:=Kernel(mix);;
Print("index of even-product-sign subgroup L' in A: ",Size(A)/Size(Lp),"\n");;
Print("L' transitive on W: ",IsTransitive(Lp,Wpts),"\n");;
w0:=1;;
stab:=Stabilizer(Lp,w0);;
orbs:=Orbits(stab,Difference(Wpts,[w0]));;
Print("L' suborbit lengths: ",SortedList(List(orbs,Length)),"\n");;
sizes:=[];;
for o in orbs do b:=Blocks(Lp,Wpts,[w0,o[1]]); AddSet(sizes,Length(b[1])); od;;
Print("L' minimal block sizes: ",sizes,"\n");;
nontriv:=First(List(orbs,o->Blocks(Lp,Wpts,[w0,o[1]])),b->Length(b[1])>1 and Length(b)>1);;
acting:=Action(Lp,nontriv,OnSets);;
Print("L' block quotient order ",Size(acting)," on ",Length(nontriv)," blocks, primitive ",IsPrimitive(acting),"\n");;
