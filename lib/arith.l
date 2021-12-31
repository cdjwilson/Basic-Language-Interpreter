addn(zero, zero, zero).
addn(succ(M), zero, succ(P)) :- addn(M, zero, P).
addn(zero, succ(N), succ(P)) :- addn(zero, N, P).
addn(succ(M), succ(N), succ(P)) :- addn(M, succ(N), P).

multn(zero, N, zero).
multn(succ(M), N, P) :- multn(M, N, Z), addn(Z, N, P).

int(M, N).

eqi(int(zero, zero), int(zero, zero)).
eqi(int(zero, zero), int(succ(K), succ(L))) :- eqi(int(zero, zero), int(K, L)).
eqi(int(succ(I), succ(J)), int(zero, zero)) :- eqi(int(I, J), int(zero, zero)).
eqi(int(succ(I), zero), int(succ(K), zero)) :- eqi(int(I, zero), int(K, zero)).
eqi(int(zero, succ(J)), int(zero, succ(L))) :- eqi(int(zero, J), int(zero, L)).
eqi(int(succ(I), succ(J)), int(succ(K), zero)) :- eqi(int(I, J), int(succ(K), zero)).
eqi(int(succ(I), succ(J)), int(zero, succ(L))) :- eqi(int(I, J), int(zero, succ(L))).
eqi(int(succ(I), zero), int(succ(K), succ(L))) :- eqi(int(succ(I), zero), int(K, L)).
eqi(int(zero, succ(J)), int(succ(K), succ(L))) :- eqi(int(zero, succ(J)), int(K, L)).
eqi(int(succ(I), succ(J)), int(succ(K), succ(L))) :- eqi(int(I, J), int(K, L)).

addi(int(I, J), int(zero, zero), M) :- eqi(int(I, J), M).
addi(int(I, J), int(zero, succ(L)), M) :- addi(int(I, succ(J)), int(zero,L), M).
addi(int(I, J), int(succ(K), zero), M) :- addi(int(succ(I), J), int(K,zero), M).
addi(int(I, J), int(succ(K), succ(L)), M) :- addi(int(succ(I), succ(J)), int(K,L), M).

multi(int(zero, zero), int(zero, zero), int(zero, zero)).
multi(int(zero, succ(J)), int(zero, succ(N)), int(succ(K), zero)) :- multn(succ(J), succ(N), succ(K)).
multi(int(zero, succ(J)), int(succ(M), zero), int(zero, succ(L))) :- multn(succ(J), succ(M), succ(L)).
multi(int(succ(I), zero), int(zero, succ(N)), int(zero, succ(L))) :- multn(succ(I), succ(N), succ(L)).
multi(int(succ(I), zero), int(succ(M), zero), int(succ(K), zero)) :- multn(succ(I), succ(M), succ(K)).
multi(int(zero, succ(J)), int(succ(M), succ(N)), int(zero, succ(L))) :- multi(int(zero, succ(J)), int(M, N), int(zero, succ(L))).
multi(int(zero, succ(J)), int(succ(M), succ(N)), int(succ(K), zero)) :- multi(int(zero, succ(J)), int(M, N), int(succ(K), zero)).
multi(int(zero, succ(J)), int(succ(M), succ(N)), int(succ(K), succ(L))) :- multi(int(zero, succ(J)), int(M, N), int(K, L)).
multi(int(succ(I), zero), int(succ(M), succ(N)), int(zero, succ(L))) :- multi(int(succ(I), zero), int(M, N), int(zero, succ(L))).
multi(int(succ(I), zero), int(succ(M), succ(N)), int(succ(K), zero)) :- multi(int(succ(I), zero), int(M, N), int(succ(K), zero)).
multi(int(succ(I), zero), int(succ(M), succ(N)), int(succ(K), succ(L))) :- multi(int(succ(I), zero), int(M, N), int(K, L)).
multi(int(succ(I), succ(J)), int(zero, succ(N)), int(zero, succ(L))) :- multi(int(I, J), int(zero, succ(N)), int(zero, succ(L))).
multi(int(succ(I), succ(J)), int(zero, succ(N)), int(succ(K), zero)) :- multi(int(I, J), int(zero, succ(N)), int(succ(K), zero)).
multi(int(succ(I), succ(J)), int(zero, succ(N)), int(succ(K), succ(L))) :- multi(int(I, J), int(zero, succ(N)), int(K, L)).
multi(int(succ(I), succ(J)), int(succ(M), zero), int(zero, succ(L))) :- multi(int(I, J), int(succ(M), zero), int(zero, succ(L))).
multi(int(succ(I), succ(J)), int(succ(M), zero), int(succ(K), zero)) :- multi(int(I, J), int(succ(M), zero), int(succ(K), zero)).
multi(int(succ(I), succ(J)), int(succ(M), zero), int(succ(K), int(succ(L)))) :- multi(int(I, J), int(succ(M), zero), int(K, L)).
multi(int(succ(I), succ(J)), int(succ(M), succ(N)), int(succ(K), succ(L))) :- multi(int(I, J), int(M, N), int(K, L)).

inverse(int(zero, zero), int(zero, zero)).
inverse(int(zero, succ(J)), int(succ(L), zero)) :- inverse(int(zero, J), int(L, zero)).
inverse(int(succ(I), zero), int(zero, succ(M))) :- inverse(int(I, zero), int(zero, M)).
inverse(int(zero, succ(J)), int(succ(L), succ(M))) :- inverse(int(zero, succ(J)), int(L, M)).
inverse(int(succ(I), zero), int(succ(L), succ(M))) :- inverse(int(succ(I), zero), int(L, M)).
inverse(int(succ(I), succ(J)), int(zero, succ(M))) :- inverse(int(I, J), int(zero, succ(M))).
inverse(int(succ(I), succ(J)), int(succ(L), zero)) :- inverse(int(I, J), int(succ(L), zero)).
inverse(int(succ(I), succ(J)), int(zero, zero)) :- inverse(int(I, J), int(zero, zero)).
inverse(int(zero, zero), int(succ(L), succ(M))) :- inverse(int(zero, zero), int(L, M)).
inverse(int(succ(I), succ(J)), int(succ(L), succ(M))) :- inverse(int(I, J), int(L, M)).