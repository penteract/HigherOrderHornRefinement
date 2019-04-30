                                             
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
GenConsume : ((((o -> o) -> o -> o) -> o) -> o) -> (((o -> o) -> o -> o) -> o -> o) -> (((o -> o) -> o -> o) -> o -> o) -> o -> o;
Use : (((o -> o) -> o -> o) -> o -> o) -> (((o -> o) -> o -> o) -> o -> o) -> o -> ((o -> o) -> o -> o) -> o;
Loop : (((o -> o) -> o -> o) -> o -> o) -> ((o -> o) -> o -> o) -> o -> o;
I : (o -> o) -> o -> o;
K : (o -> o) -> o -> o;
Newr : (((o -> o) -> o -> o) -> o) -> o;
Neww : (((o -> o) -> o -> o) -> o) -> o;
Close : ((o -> o) -> o -> o) -> o -> o;
Read : ((o -> o) -> o -> o) -> o -> o;
Write : ((o -> o) -> o -> o) -> o -> o;
}

rules {
S = GenConsume Newr Read Close (GenConsume Neww Write Close end);
GenConsume gen use finish k = gen (Use use finish k);
Use use finish k x = Loop use x (finish x k);
Loop use x k = br k (Loop use x (use x k)); 
I x y = x y;
K x y = y;
Newr k = br (newr (k I)) (k K);
Neww k = br (neww (k I)) (k K);
Close x k = x close k;
Read x k = x read k;
Write y k = y write k;
}

transitions{
q0,br -> q0 q0;
q0,neww -> q0;
q0,read -> q0;
q0,close -> q0;
q0,end -> ;
q0,write -> q0;
q0,newr -> qnewr;
qnewr, br -> qnewr qnewr;
qnewr, neww -> qnewr;
qnewr, close -> qnewr;
qnewr, write -> qnewr;
qnewr, end -> ;
qnewr, read -> qrd;
qrd, read -> qrd;
qrd, close -> qtrue;
qtrue, br -> qtrue qtrue;
qtrue, neww -> qtrue;
qtrue, newr -> qtrue;
qtrue, read -> qtrue;
qtrue, write -> qtrue;
qtrue, close -> qtrue;
qtrue, end -> ;
}

acceptance{
accept : qtrue;
reject : qrd;
accept : q0 qnewr;
}

