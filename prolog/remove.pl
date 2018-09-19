remove([],W,[]).
remove([X|Xs],X,Z) :- remove(Xs,X,Z).
remove([X|Xs],Y,[X|Z]) :- X\=Y, remove(Xs,Y,Z).

# remove([],W,[]).
# remove([X|Xs],Y,Z) :- X==Y, remove(Xs,Y,Z).
# remove([X|Xs],Y,[X|Z]) :- X\=Y, remove(Xs,Y,Z).