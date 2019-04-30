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
   G k x = br (Close x k) (Read x (G k x));

   // Transform plumbing
   I x y = x y;
   K x y = y;
   Newr k = brnew (newr (k I)) (k K);
   Close x k = x close k;
   Read x k = x read k;
}

transitions {
    qir,brnew -> (1,qir) (2,qir);
    qir,newr -> (1,qir); // Start monitoring resource
    qir,br -> (1,ql) (2,qir);
    qir,read -> (1,qir);
    qir,close -> ;
    qir,end -> ;
    
    ql,read -> (1,ql);
    ql,br -> (1,ql) (2,ql);
    ql,close -> ; // Satisfied
    ql,end -> ;
}

acceptance {
    reject : ql;
    accept : qir;
}
