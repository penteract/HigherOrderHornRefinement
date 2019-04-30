terminals {
    br     : o -> o -> o;
    newr   : o -> o;
    neww   : o -> o;
    read   : o -> o;
    write  : o -> o;
    closer : o -> o;
    closew : o -> o;
    end    : o;
}

nonterminals {
    S      : o;
    C1     : ((o -> o) -> o -> o) -> o;
    C2     : ((o -> o) -> o -> o) -> ((o -> o) -> o -> o) -> o;
    F      : ((o -> o) -> o -> o) -> ((o -> o) -> o -> o) -> ((o -> o) -> o -> o) -> o -> o;
    G      : ((o -> o) -> o -> o) -> ((o -> o) -> o -> o) -> o -> o;
    I      : (o -> o) -> o -> o;
    K      : (o -> o) -> o -> o;
    Newr   : (((o -> o) -> o -> o) -> o) -> o;
    Neww   : (((o -> o) -> o -> o) -> o) -> o;
    Closer : ((o -> o) -> o -> o) -> o -> o;
    Closew : ((o -> o) -> o -> o) -> o -> o;
    Read   : ((o -> o) -> o -> o) -> o -> o;
    Write  : ((o -> o) -> o -> o) -> o -> o;
    Zero   : (o -> o) -> o -> o;
    Succ   : ((o -> o) -> o -> o) -> (o -> o) -> o -> o;
}

rules {
    // Program functions
    S           = Newr C1;
    C1 x        = Neww (C2 x);
    C2 x y      = F x y Zero end;
    F x y n k   = br (Read x (F x y (Succ n) k)) (Closer x (G y n k));
    G y n k     = n (Write y) (Closew y k);
    
    // Transform plumbing (we always want both resources here)
    I x y = x y;
    K x y = y;
    Newr k = newr (k I);
    Neww k = neww (k I);
    Closer x k = x closer k;
    Closew x k = x closew k;
    Read x k = x read k;
    Write x k = x write k;
    
    // Church numerals
    Zero f x = x;
    Succ n f x = f (n f x);
}

// AG (closer -> F closew)
transitions {
    q0,newr -> (1,q0);
    q0,neww -> (1,q0);
    q0,br -> (1,q0) (2,q0);
    q0,read -> (1,q0);
    q0,write -> (1,q0);
    q0,closer -> (1,qf) (1,q0); // Check (F closew), and also keep AG running
    q0,closew -> (1,q0);
    q0,end -> ;
    
    qf,newr -> (1,qf);
    qf,neww -> (1,qf);
    qf,br -> (1,qf) (2,qf);
    qf,read -> (1,qf);
    qf,write -> (1,qf);
    qf,closer -> (1,qf);
    qf,closew -> ;              // Accept the closew
}


acceptance {
    reject : qf;
    accept : q0;
}

