terminals {
br : o -> o -> o;
newr : o -> o;
read : o -> o;
close : o -> o;
neww : o -> o;
write : o -> o;
end : o;
}

nonterminals {
S : o;
F1 : o;
GenConsume : o;
C : o;
I : o;
K : o;
Newr : o;
Close : o;
Read : o;
}



rules {
S = GenConsume Newr F1 end; 
F1 x k = br (Close x k) (Read x (F1 x k));
GenConsume gen use k = br k (GenConsume gen use (gen (C use k)));
C use k x = use x k;
I x y = x y;
K x y = y;
Newr k = br (newr (k I)) (k K);
Close x k = x close k;
Read x k = x read k;
}


transitions{
q0,br -> q0 q0;
qr,br -> qr qr;
qw,br -> qw qw;
qrw,br -> qrw qrw;
q0,newr -> qr;
qr,read -> qr;
qr,close -> qc;
qc,br -> qc qc;
q0,neww -> qw;
qw,write -> qw;
qw,close -> qc;
qw,newr -> qrw;
qr,neww -> qrw;
qc,newr -> qrw;
qc,neww -> qrw;
qrw,newr -> qrw;
qrw,neww -> qrw;
qrw,read -> qrw;
qrw,write -> qrw;
qrw,close -> qrw;
qc,end ->;
q0,end ->;
qrw,end ->;
}


