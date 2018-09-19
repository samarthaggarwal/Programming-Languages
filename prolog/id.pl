id([],[]).
id([X|Xs],[X|Ys]) :- X>6, id(Xs,Ys).
