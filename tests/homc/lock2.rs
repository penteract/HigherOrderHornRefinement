terminals {
br : o -> o -> o;
newl : o -> o;
lock : o -> o;
unlock : o -> o;
end : o;
}

nonterminals {
S : o;
C1 : o;
Unlock : o;
Lock : o;
C2 : o;
F : o;
C3 : o;
C4 : o;
NewL : o;
I : o;
K : o;
}


rules {  
S = NewL C1;
C1 x = C2 (Unlock x) (Lock x);
Unlock x k = x unlock k;
Lock x k = x lock k;
C2 h1 h2 = h2(F h1 end);
F g k = br (g k) (NewL (C3 g k));
C3 g k x = C4 g (Unlock x) (Lock x) k;
C4 g h1 h2 k = h2(F h1 (g k));
NewL k = br (newl (k I)) (k K);
I x y = x y;
K x y = y;
}


transitions{
q0,br -> q0 q0;
q1,br -> q1 q1;
q2,br -> q2 q2;
qany,br -> qany qany;
q0,newl -> q1;
q1,newl -> qany;
q2,newl -> qany;
qany,lock -> qany;
qany,newl -> qany;
qany,unlock -> qany;
qany,end -> ;
q1,lock -> q2;
q2,unlock -> q1;
q0,end -> ;
q1,end -> ;
}


