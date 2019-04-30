terminals {
    br : o -> o -> o;
    newl : o -> o;
    lock : o -> o;
    unlock : o -> o;
    end : o;
}

nonterminals {
    S  : o;
    C0 : ((o -> o) -> o -> o) -> o;
    C1 : ((o -> o) -> o -> o) -> o;
    F0 : ((o -> o) -> o -> o) -> o -> o;
    F1 : ((o -> o) -> o -> o) -> o -> o;
    G0 : ((o -> o) -> o -> o) -> o -> o;
    G1 : ((o -> o) -> o -> o) -> o -> o;
    New : (((o -> o) -> o -> o) -> o) -> o;
    I  : (o -> o) -> o -> o;
    K : (o -> o) -> o -> o;
    Lock : ((o -> o) -> o -> o) -> o -> o;
    Unlock : ((o -> o) -> o -> o) -> o -> o;
}

rules {
S = br (New C0) (New C1);
C0 x = F0 x (G0 x end);
C1 x = F1 x (G1 x end);
F0 x k = k;
F1 x k = Lock x k;
G0 x k = k;
G1 x k = Unlock x k;
New k = br (newl (k I)) (k K);
I x y = x y;
K x y = y;
Lock x k = x lock k;
Unlock x k = x unlock k;
}

transitions {
q0,br -> q0 q0;
q1,br -> q1 q1;
q2,br -> q2 q2;
q0,newl -> q1;
q1,lock -> q2;
q2,unlock -> q1;
q0,end -> ;
q1,end -> ;
}
