:- discontiguous ex/1.
:- discontiguous nex/1.
:- discontiguous parent/2.
:- discontiguous male/1.
:- discontiguous female/1.
:- discontiguous backliteral/2.
:- discontiguous prolog_predicate/1.
:- discontiguous start_hyp/1.
:- discontiguous prove/3.
:- discontiguous prove_goal/4.
:- discontiguous induce/1.
:- discontiguous iter_deep/3.
:- discontiguous depth_first/3.
:- discontiguous complete/1.
:- discontiguous consistent/1.
:- discontiguous refine_hyp/2.
:- discontiguous refine/4.
:- discontiguous max_proof_length/1.
:- discontiguous max_clause_length/1.

ex(predecessor(pam, bob)).
ex(predecessor(pam, jim)).
ex(predecessor(tom, ann)).
ex(predecessor(tom, jim)).
ex(predecessor(tom, liz)).

nex(predecessor(liz, bob)).
nex(predecessor(pat, bob)).
nex(predecessor(pam, liz)).
nex(predecessor(liz, jim)).
nex(predecessor(liz, liz)).

parent(pam, bob).
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).
parent(pat, eve).

male(tom).
male(bob).
male(jim).
female(pam).
female(liz).
female(ann).
female(pat).
female(eve).

backliteral([atom(X), parent(X, Y)], [X, Y]).
backliteral([atom(X), predecessor(X, Y)], [X, Y]).
prolog_predicate(parent(_, _)).
prolog_predicate(atom(_)).

start_hyp([
    [predecessor(A, B), [atom(A), parent(A, C)], [atom(C), predecessor(C, B)]] / [A, C, B],
    [predecessor(D, E), [atom(D), parent(D, E)]] / [D, E]
]).

prove(Goal, Hypo, Answer) :-
    max_proof_length(D),
    prove_goal(Goal, Hypo, D, RestD),
    (RestD >= 0 -> Answer = true ; RestD < 0 -> Answer = maybe).
prove(_, _, false).

prove_goal(_, _, D, D) :- D < 0, !.
prove_goal([], _, D, D) :- !.
prove_goal([G1 | Gs], Hypo, D0, D) :-
    prove_goal(G1, Hypo, D0, D1),
    prove_goal(Gs, Hypo, D1, D).
prove_goal(G, _, D, D) :-
    prolog_predicate(G),
    (G = parent(X, Y) -> parent(X, Y) ; G = atom(X), atom(X)).
prove_goal(G, Hypo, D0, D) :-
    D0 > 0,
    D1 is D0 - 1,
    member(Clause / _, Hypo),
    copy_term(Clause, [Head | Body]),
    G = Head,
    prove_goal(Body, Hypo, D1, D).

max_depth_limit(20).

induce(Hyp) :-
    max_depth_limit(Limit),
    iter_deep(Hyp, 0, Limit).

iter_deep(Hyp, MaxD, Limit) :-
    (MaxD =< Limit ->
        start_hyp(Hyp0),
        (complete(Hyp0) ->
            depth_first(Hyp0, Hyp, MaxD)
        ;
            NewMaxD is MaxD + 1,
            iter_deep(Hyp, NewMaxD, Limit)
        )
    ;
        write('Reached maximum depth limit of '), write(Limit), nl, fail).

depth_first(Hyp, Hyp, _) :-
    consistent(Hyp).
depth_first(Hyp0, Hyp, MaxD0) :-
    MaxD0 > 0,
    MaxD1 is MaxD0 - 1,
    refine_hyp(Hyp0, Hyp1),
    complete(Hyp1),
    depth_first(Hyp1, Hyp, MaxD1).

complete(Hyp) :-
    \+ (ex(E), \+ prove_goal(E, Hyp, 10, _)).

consistent(Hyp) :-
    \+ (nex(E), prove_goal(E, Hyp, 10, _)).

refine_hyp(Hyp0, Hyp) :-
    append(Clauses1, [Clause0 / _ | Clauses2], Hyp0),
    append(Clauses1, [Clause / _ | Clauses2], Hyp),
    refine(Clause0, _, Clause, _).

refine(Clause, Args, Clause, NewArgs) :-
    append(Args1, [_ | Args2], Args),
    append(Args1, Args2, NewArgs).

refine(Clause, Args, NewClause, NewArgs) :-
    length(Clause, L),
    max_clause_length(MaxL),
    L < MaxL,
    backliteral(Lit, Vars),
    append(Clause, [Lit], NewClause),
    append(Args, Vars, NewArgs).

max_proof_length(10).
max_clause_length(3).
