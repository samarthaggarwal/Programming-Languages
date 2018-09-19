edge(a,b).
edge(a,c).
edge(b,d).
edge(b,e).
edge(c,e).
edge(c,f).
edge(e,g).
edge(f,h).
edge(i,c).
path(X,X).
path(X,Y) :- edge(X,Z) , path(Z,Y).