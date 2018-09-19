member(X,[]) :- fail.
member(X,[X|Xs]).
member(X,[Y|Ys]) :- member(X,Ys).