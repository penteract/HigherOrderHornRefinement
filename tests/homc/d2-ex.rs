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
    qm,brnew -> (1,qm) (2,qm);
    qm,newr -> (1,qm) (1,q0);    
    q0,br -> (1,q1);
    q0,br -> (2,q1);
    q1,close -> ;
    
    qm,br -> (1,qm) (2,qm);
    qm,read -> (1,qm);          
    qm,close -> (1,qm);             
    qm,end -> ;
}


acceptance {
    accept : q0 q1 qm;
}
