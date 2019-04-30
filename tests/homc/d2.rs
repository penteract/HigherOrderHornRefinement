terminals {
   brnew : o -> o -> o;
   br : o -> o -> o;
   newr : o -> o;
   read : o -> o;
   close : o -> o;
   end : o;
}

nonterminals {
   S     : o;
   G     : o -> ((o -> o) -> o -> o) -> o;
   I     : (o -> o) -> o -> o;
   K     : (o -> o) -> o -> o;
   Newr  : (((o -> o) -> o -> o) -> o) -> o;
   Close : ((o -> o) -> o -> o) -> o -> o;
   Read  : ((o -> o) -> o -> o) -> o -> o;
}

rules {
   // Program functions
   S     = Newr (G end);
   G k x = br (Close x (Newr (G end))) (Read x (G k x));

   // Transform plumbing
   I x y = x y;
   K x y = y;
   Newr k = brnew (newr (k I)) (k K);
   Close x k = x close k;
   Read x k = x read k;
}

transitions {
    q0,brnew -> (1,q0) (2,q0);
    q0,newr -> (1,qir) (1,q0);    // Start monitoring, wait for next resource
    q0,br -> (1,q0) (2,q0);
    q0,read -> (1,q0);
    q0,close -> (1,q0);
    q0,end -> ;
    
    qir,br -> (1,ql) (2,qir);
    qir,read -> (1,qir);          // Start r U c
    qir,close -> ;               // Satisfied
    qir,end -> ;

    ql,read -> (1,ql);
    ql,br -> (1,ql) (2,ql);
    ql,close -> ; // Satisfied
    ql,end -> ;
}


acceptance {
    reject : ql;
    accept : q0 qir;
}
