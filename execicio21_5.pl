:- discontiguous ex/1.
:- discontiguous nex/1.
:- discontiguous backliteral/3.
:- discontiguous term/3.
:- discontiguous start_clause/1.
:- discontiguous max_clauses/1.

backliteral(member(X, L), [L:list], [X:item]).

term(list, [X|L], [X:item, L:list]).
term(list, [], []).

start_clause([member(X, L)] / [X:item, L:list]).

start_hyp([
    [member(X, L)] / [X:item, L:list]
]).

ex(member(a, [a])).
ex(member(b, [a, b])).
ex(member(d, [a, b, c, d, e])).

nex(member(b, [a])).
nex(member(d, [a, b])).
nex(member(f, [a, b, c, d, e])).

max_proof_length(10).
max_clause_length(3).
max_clauses(2).
max_depth_limit(50). 

prove(Goal, Hypo, Answer) :-
    max_proof_length(D),
    prove_goal(Goal, Hypo, D, RestD),
    (RestD >= 0 -> Answer = yes ; RestD < 0 -> Answer = maybe).
prove(_, _, no).

prove_goal(_, _, D, D) :- D < 0, !.
prove_goal([], _, D, D) :- !.
prove_goal([G1 | Gs], Hypo, D0, D) :-
    prove_goal(G1, Hypo, D0, D1),
    prove_goal(Gs, Hypo, D1, D).
prove_goal(member(X, L), _, D, D) :-
    member(X, L).
prove_goal(G, Hypo, D0, D) :-
    D0 > 0,
    D1 is D0 - 1,
    member(Clause / _Vars, Hypo),
    copy_term(Clause, [Head | Body]),
    G = Head,
    prove_goal(Body, Hypo, D1, D).

induce(Hyp) :-
    max_depth_limit(Limit),
    iter_deep(Hyp, 0, Limit).

iter_deep(Hyp, MaxD, Limit) :-
    (MaxD =< Limit ->
        start_hyp(Hyp0),
        complete(Hyp0),
        depth_first(Hyp0, Hyp, MaxD)
    ;
        NewMaxD is MaxD + 1,
        iter_deep(Hyp, NewMaxD, Limit)
    ).

depth_first(Hyp, Hyp, _) :-
    consistent(Hyp).
depth_first(Hyp0, Hyp, MaxD0) :-
    MaxD0 > 0,
    MaxD1 is MaxD0 - 1,
    refine_hyp(Hyp0, Hyp1),
    complete(Hyp1),
    depth_first(Hyp1, Hyp, MaxD1).

complete(Hyp) :-
    \+ (ex(E), \+ prove_goal(E, Hyp, 10, _)),
    format("Hipótese completa para exemplos positivos: ~w~n", [Hyp]).

consistent(Hyp) :-
    \+ (nex(E), prove_goal(E, Hyp, 10, Answer), Answer == yes),
    format("Hipótese consistente para exemplos negativos: ~w~n", [Hyp]).

refine_hyp(Hyp0, Hyp) :-
    append(Clauses1, [Clause0 / _Vars0 | Clauses2], Hyp0),
    append(Clauses1, [Clause / Vars | Clauses2], Hyp),
    refine(Clause0, Vars, Clause, Vars).

refine(Clause, Args, Clause, NewArgs) :-
    append(Args1, [A | Args2], Args),
    member(A, Args2),
    append(Args1, Args2, NewArgs).

refine(Clause, Args, NewClause, NewArgs) :-
    length(Clause, L),
    max_clause_length(MaxL),
    L < MaxL,
    backliteral(Lit, Vars, _),
    append(Clause, [Lit], NewClause),
    append(Args, Vars, NewArgs).

conc([], L, L).
conc([X | T], L, [X | L1]) :-
    conc(T, L, L1).

not(A, B, C) :-
    A,
    B,
    C, !, fail.
not(_, _, _).

