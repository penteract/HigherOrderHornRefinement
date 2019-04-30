// This example is based on the imperative program introduced at the start
// of section 3 of "Branching-time reasoning for infinite-state systems"
// by Cook, Koskinen and Vardi.

terminals {
    end   : o;
    set_x_one   : o -> o;
    decr  : o -> o;
    loop  : o -> o;
    set_x_zero : o -> o;
    br    : o -> o -> o;
}

nonterminals {
    S : o;
    EnterLoop : o;
    IncCounter : ((o -> o) -> o -> o) -> o -> o;
    RunLoop : ((o -> o) -> o -> o) -> o -> o;
    Loop : o -> o;
    Zero : (o -> o) -> o -> o;
    Succ : ((o -> o) -> o -> o) -> (o -> o) -> o -> o;
}

rules {
    S = br EnterLoop end;
    EnterLoop = set_x_one (IncCounter Zero (Loop end));
    IncCounter n f = br (RunLoop n f) (IncCounter (Succ n) f);
    RunLoop n f = n decr (set_x_zero f);
    Zero f x = x;
    Succ n f x = f (n f x);
    Loop k = loop (Loop k);
}

transitions {
    q0, set_x_one -> q0;
    q0, set_x_zero -> qc;
    q0, end -> ;
    q0, decr -> qr;
    q0, br -> q0 q0;
    
    qr, set_x_zero -> qc;
    qr, br -> qr qr;
    qr, decr -> qr;  
    
    qc, loop -> qc;
}

acceptance {
    accept : qc;
    reject : qr;
    accept : q0;
}
