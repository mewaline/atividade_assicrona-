prove(Goal, Hypo, Answer):-
    max_proof_length(D),
    prove(Goal, Hypo, D, RestD),
    (RestD >= 0, Answer = yes
     ;                     
     RestD < 0, Answer = maybe).
prove(_, _, no).

prove(_, _, D, D):-
    D < 0, !.
prove([], _, D, D):- !.
prove([G1|Gs],Hypo,D0,D):-
    prove(G1,Hypo,D0,D1),
    prove(Gs,Hypo,D1,D).
prove(G,_,D,D):-
    prolog_predicate(G),
    call(G).
prove(G,Hypo,D0,D):-
    D0 =< 0, !,
    D is D0-1;
    D1 is D0 - 1,
    member(Clause/_ , Hypo),
    copy_term(Clause, [Head|Body]),
    G = Head,
    prove(Body, Hypo, D1, D).

induce(Hyp):-
    iter_deep(Hyp,0).

iter_deep(Hyp,MaxD):-
    write('MaxD= '), write(MaxD), nl,
    start_hyp(Hyp0),
    complete(Hyp0),
    depth_first(Hyp0,Hyp,MaxD);
    NewMaxD is MaxD+1,
    iter_deep(Hyp, NewMaxD).

depth_first(Hyp,Hyp,_):-
    consistent(Hyp).
depth_first(Hyp0,Hyp,MaxD0):-
    MaxD0 > 0,
    MaxD1 is MaxD0-1,
    refine_hyp(Hyp0, Hyp1),
    complete(Hyp1),
    depth_first(Hyp1,Hyp,MaxD1).

complete(Hyp):-
    not((ex(E),
        once(prove(E, Hyp, Answer)),
        Answer \== yes)).

consistent(Hyp):-
    not((nex(E),
        once(prove(E, Hyp, Answer)),
        Answer \== no)).

refine_hyp(Hyp0,Hyp):-
    conc(Clauses1,[Clause0/_ | Clauses2], Hyp0),
    conc(Clauses1,[Clause/_ | Clauses2], Hyp),
    refine(Clause0, _, Clause, _).

refine(Clause, Args, Clause, NewArgs):-
    conc(Args1, [_ | Args2], Args),
    conc(Args1, Args2, NewArgs).
refine(Clause,Args,NewClause, NewArgs):-
    length(Clause, L),
    max_clause_length(MaxL),
    L < MaxL,
    backliteral(Lit, Vars),
    conc(Clause,[Lit],NewClause),
    conc(Args, Vars, NewArgs).

max_proof_length(10).
max_clause_length(3).

conc([],L,L).
conc([X|T],L,[X|L1]):-
    conc(T,L,L1).

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

start_hyp([[predecessor(X1,Y1)]/[X1,Y1], [predecessor(X2,Y2)]/[X2,Y2]]).

backliteral(parent(X,Y), [X,Y]).
backliteral(predecessor(X,Y), [X,Y]).

prolog_predicate(parent(_,_)).
