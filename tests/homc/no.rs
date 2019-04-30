terminals {
    f:o -> o -> o;
    g:o -> o;
    a:o;
}

nonterminals {
    S : o;
}


rules {
S = f (g (f a a)) a;
}

transitions {
q0, f -> q0 q0;
q0, g -> q1;
q1, g -> q1;
q0, a -> ;
q1, a -> ;
}
