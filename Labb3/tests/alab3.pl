:- use_module(library(lists)).
:- discontiguous check/5.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).
% Literals
ok(_,_,[],_,_).
ok(T,L,[H|R],U,F):-check(T,L,H,U,F),ok(T,L,R,U,F).

check(_, L, S, [], X):- member([S, List], L), member(X, List).
check(_, L, S, [], neg(X)):- member([S, List], L), \+member(X, List).
% And
check(T, L, S, U, and(F,G)):- check(T, L, S, [], F), check(T, L, S, [], G).
% Or
check(T, L, S, U, or(F,G)):- check(T, L, S, [], F).
check(T, L, S, U, or(F,G)):- check(T, L, S, [], G).
% AX
check(T, L, S, [], ax(F)) :- member([S, List], T),
                        ok(T,L,List,[], F).
% EX
check(T, L, S, [], ex(F)) :- member([S, List], T), 
                        member(New, List), check(T,L,New,[],F).
check(_, _, S, U, ag(_)) :- member(S, U).
check(T, L, S, U, ag(F)) :- \+member(S,U),
    check(T, L, S, [], F),
    member([S,List], T),
    ok(T,L,List,[S|U],ag(F)).
% EG - For some path from S, F becomes true and stays true from that point on.
check(_, _, S, U, eg(_)):- member(S, U).
check(T,L,S,U,eg(F)):- \+member(S,U),
                        check(T,L,S,[],F),
                        member([S,P],T),
                        member(New,P),
                        check(T,L,New,[S|U],eg(F)).

% EF - For some future path P from S, F becomes true. 
check(T,L,S,U,ef(F)):- \+member(S,U), check(T,L,S,[],F).
check(T,L,S,U,ef(F)):- \+member(S,U), member([S,P],T),
                        member(S2,P),
                        check(T,L,S2,[S|U],ef(F)).
% AF - For all future paths from S, F becomes true.
check(T,L,S,U,af(F)):- \+member(S,U),
                        check(T,L,S,[],F).
check(T,L,S,U,af(F)):- \+member(S,U),
                        member([S,List],T),
                        ok(T,L,List,[S|U], af(F)).