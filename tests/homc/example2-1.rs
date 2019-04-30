terminals {
    a:o -> o -> o;
    b:o -> o;
    c:o;
}

nonterminals {
    S : o;
    F : o->o;
}


rules {
S = F c;
F x = a x (F (b x));
}


transitions {
q0,a -> q0 q0;
q0,b -> q1;
q1,b -> q1;
q0,c -> ;
q1,c -> ;
}
