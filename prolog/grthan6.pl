check([],[]).
check([X|Xs],Ys) :- X=<6 , check(Xs,Ys).
check([X|Xs],[X|Ys]) :- X>6 , check(Xs,Ys).
