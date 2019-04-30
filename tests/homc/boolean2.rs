
terminals {
    end : o;
    fail : o;
    br : o -> o -> o;
}

nonterminals {
    S : o;
    L1_1 : o;
    L1_2 : (o -> o -> o) -> o;
    L1_3 : (o -> o -> o) -> (o -> o -> o) -> o;
    L2 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L3 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L4 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L5 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L6 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L7 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L8 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L9 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    L10 : (o -> o -> o) -> (o -> o -> o) -> (o -> o -> o) -> o;
    True : o -> o -> o;
    False : o -> o -> o;
}


rules {
    S = L1_1;
    L1_1 = br (L1_2 True) (L1_2 False);
    L1_2 x = br (L1_3 x True) (L1_3 x False);
    L1_3 x y = br (L2 x y True) (L2 x y False);
    L2 x y z = L3 x y True;
    L3 x y z = L4 True y z;
    L4 x y z = y (L5 x y z) (L7 x y z);
    L5 x y z = L6 False y z;
    L6 x y z = L7 x y True;
    L7 x y z = x (L9 x y z) (L8 x y z);
    L8 x y z = L10 x y z;
    L9 x y z = L2 x y z;
    L10 x y z = z end fail;

    True x y  = x;
    False x y = y;
}

transitions {
    q0, br -> q0 q0;
    q0, end -> ;
}
