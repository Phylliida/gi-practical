# The Case-1 wreath outcome: Sym(a) wr C2 on the cross pairs of labels.
a:=4;;
B1:=[1..a];; B2:=[a+1..2*a];;
G:=Group(List(GeneratorsOfGroup(SymmetricGroup(B1)),x->x));;
G:=ClosureGroup(G,GeneratorsOfGroup(SymmetricGroup(B2)));;
G:=ClosureGroup(G,PermList(Concatenation(B2,B1)));;
Print("|Sym(",a,") wr C2| = ",Size(G),"\n");;
pairs:=Set(Concatenation(List(B1,x->List(B2,y->Set([x,y])))));;
P:=Action(G,pairs,OnSets);;
Print("action on unordered cross pairs: degree ",NrMovedPoints(P),", primitive ",IsPrimitive(P),", order ",Size(P),"\n");;
Print("is it natural or 2-subset alternating/symmetric? ",IsNaturalAlternatingGroup(P) or IsNaturalSymmetricGroup(P),"\n");;
Print("structure: ",StructureDescription(P),"\n");;
# the actual HJ continuation group intersects with Alt(2a); check at a=5 (Alt(a)^2 socle needs a>=5)
a:=5;;
B1:=[1..a];; B2:=[a+1..2*a];;
G:=ClosureGroup(Group(GeneratorsOfGroup(SymmetricGroup(B1))),GeneratorsOfGroup(SymmetricGroup(B2)));;
G:=ClosureGroup(G,PermList(Concatenation(B2,B1)));;
H:=Intersection(G,AlternatingGroup([1..2*a]));;
pairs:=Set(Concatenation(List(B1,x->List(B2,y->Set([x,y])))));;
P:=Action(H,pairs,OnSets);;
Print("a=",a,": (Sym(a) wr C2) cap Alt(2a) on unordered cross pairs: degree ",NrMovedPoints(P),", transitive ",IsTransitive(P,[1..Length(pairs)]),", primitive ",IsPrimitive(P),", order ",Size(P),"\n");;
QUIT;;
