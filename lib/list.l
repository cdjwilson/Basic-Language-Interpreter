elem(X, cons(X, Ys)).
elem(X, cons(Y, Ys)) :- elem(X, Ys).

samehelp(cons(X, nil), Zs) :- elem(X, Zs).
samehelp(cons(X, Ys), Zs) :- elem(X, Zs), samehelp(Ys, Zs).
same(nil, nil).
same(X, Y) :- samehelp(X, Y), samehelp(Y, X).

length(nil, zero).
length(cons(X, Ys), succ(N)) :- length(Ys, N).

prefix(nil, Zs).
prefix(cons(X, Ys), cons(X, Zs)) :- prefix(Ys, Zs).

suffix(nil, nil).
suffix(cons(X, Xs), cons(X, Xs)).
suffix(X, cons(Y, Ys)) :- suffix(X, Ys).

append(nil, nil, nil).
append(nil, cons(Y, Ys), cons(Y, Zs)) :- append(nil, Ys, Zs).
append(cons(X, Xs), cons(Y, Ys), cons(X, Zs)) :- append(Xs, cons(Y, Ys), Zs).

reversehelptwo(nil, nil).
reversehelptwo(cons(X, Xs), cons(X, Ys)) :- reversehelptwo(Xs, Ys).
reversehelp(nil, Y, Z) :- reversehelptwo(Y, Z).
reversehelp(cons(X, Xs), Y, Z) :- reversehelp(Xs, cons(X, Y), Z).
reverse(nil, nil).
reverse(cons(X, Xs), cons(Y, Ys)) :- reversehelp(cons(X, Xs), nil, cons(Y, Ys)).

palindrome(X) :- reverse(X, X).