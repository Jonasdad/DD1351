:-discontiguous(validproof/4).
verify(InputFileName) :- see(InputFileName), read(Prems), read(Goal), read(Proof), seen, valid_proof(Prems, Goal, Proof).

getLast([], _).
getLast([A],A).
getLast([_|Tail], A):-getLast(Tail,A).

%Searches through already proven lines to see if the line is there.
find(X, [X|_]).
find(X, [_|Tail]):-find(X,Tail).

%Checks if the line is inside a box.
insidebox([[_, _, assumption]|Next],Num):-[Last|_] = Next,!,copyAllowed(Last,Num).
insidebox([_|Tail], Num):-insidebox(Tail, Num).
insidebox([[_,_,premise]|_], _).
copyAllowed(_, _):-!,false,!.
copyAllowed([Num1, _, _], Num):-Num1 =< Num.

%initiates the validproof predicate.
valid_proof(Prems, Goal, Proof):- getLast(Proof, Last), !,nth0(1,Last,Goal), validproof(Prems, Goal, Proof, []).
%Proof missing.
validproof(_, _,[], []):-!,false.
%Base case
validproof(_, _,[], _):-!.

%ASSUMPTION
validproof(Prems, Goal, [[[LineNr, X, assumption]|Next]|Rest], List):-append(List, [[LineNr, X, assumption]], NewList),!,
                                                                      validproof(Prems, Goal, Next, NewList),
                                                                      getLast(Next, Last),
                                                                      append(NewList,[Last], FinalList),!,
                                                                      validproof(Prems, Goal, Rest, FinalList).                                                                      
%NEGINT
validproof(Prems, Goal, [[LineNr, neg(X), negint(Num1, Num2)]|Next], List):-find([Num1, X, _], List),
                                                                            find([Num2, cont, _], List),
                                                                            append(List, [[LineNr, neg(X), negint(Num1, Num2)]], NewList),!,
                                                                            validproof(Prems, Goal, Next, NewList).
%IMPINT
validproof(Prems, Goal, [[LineNr, imp(X, Y), impint(Num1, Num2)]|Next], List):-find([Num1, X, assumption], List),
                                                                        find([Num2, Y, _], List),
                                                                        append(List, [[LineNr, imp(X, Y), impint(Num1,Num2)]], NewList),!,
                                                                        validproof(Prems, Goal, Next, NewList).
%PREMISE
validproof(Prems, Goal, [[Num,X,premise]|Next], List):- find(X,Prems), 
                                                        append(List, [[Num,X,premise]], NewList),!,
                                                        validproof(Prems, Goal, Next, NewList).
%ANDEL1
validproof(Prems,Goal,[[LineNr,X,andel1(Num)]|Next],List):-find([Num, and(X,_), _], List), 
                                                        append(List, [[LineNr, X, andel1(Num)]], NewList),!,
                                                        validproof(Prems, Goal, Next, NewList).
%ANDEL2
validproof(Prems,Goal,[[LineNr,X,andel2(Num)]|Next],List):-find([Num, and(_,X), _], List), 
                                                        append(List, [[LineNr, X, andel2(Num)]], NewList),!,
                                                        validproof(Prems, Goal, Next, NewList).
%ORINT1
validproof(Prems,Goal,[[LineNr,X,orint1(Num)]|Next],List):-or(A,_)=X,find([Num, A, _], List), 
                                                        append(List, [[LineNr, X, orint1(Num)]], NewList),!,
                                                        validproof(Prems, Goal, Next, NewList).
%ORINT2
validproof(Prems,Goal,[[LineNr,X,orint2(Num)]|Next],List):-or(_,B)=X,find([Num, B, _], List), 
                                                        append(List, [[LineNr, X, orint2(Num)]], NewList),!,
                                                        validproof(Prems, Goal, Next, NewList).
%ANDINT
validproof(Prems,Goal,[[LineNr,X,andint(Num1,Num2)]|Next],List):-and(A,B)=X,find([Num1, A, _], List),
                                                                find([Num2, B, _], List),
                                                                append(List, [[LineNr, X,_, andint(Num1,Num2)]], NewList),!,
                                                                validproof(Prems, Goal, Next, NewList).
%IMPEL
validproof(Prems, Goal, [[LineNr, X, impel(Num1, Num2)]|Next], List):-find([Num1, Y, _], List),
                                                                    find([Num2, imp(Y, X), _], List),
                                                                    append(List, [[LineNr, X, impel(Num1, Num2)]], NewList),!,
                                                                    validproof(Prems, Goal, Next, NewList).
%NEGEL
validproof(Prems, Goal, [[LineNr, cont, negel(Num1, Num2)]|Next], List):-find([Num1, X, _], List),
                                                                find([Num2, neg(X), _], List),
                                                                append(List, [[LineNr, cont, negel(Num1, Num2)]], NewList),!,
                                                                validproof(Prems, Goal, Next, NewList).
%CONTEL
validproof(Prems, Goal, [[LineNr, X, contel(Num)]|Next], List):-find([Num, cont, _], List),
                                                            append(List, [[LineNr, X, contel(Num)]], NewList),!,
                                                            validproof(Prems, Goal, Next, NewList).
%COPY
validproof(Prems, Goal, [[LineNr, X, copy(Num)]|Next], List):-find([Num, X, _], List),
                                                        insidebox(List, LineNr),             
                                                        append(List, [[LineNr, X, copy(Num)]], NewList),!,
                                                        validproof(Prems, Goal, Next, NewList).
%NEGNEGEL
validproof(Prems, Goal, [[LineNr, X, negnegel(Num)]|Next], List):-find([Num, neg(neg(X)), _], List),
                                                            append(List, [[LineNr, X, negnegel(Num)]], NewList),!,
                                                            validproof(Prems, Goal, Next, NewList).
%LEM
validproof(Prems, Goal, [[LineNr, or(X, neg(X)), lem]|Next], List):-append(List, [[LineNr, X, lem]], NewList),!,
                                                                validproof(Prems, Goal, Next, NewList).
%MT
validproof(Prems, Goal, [[LineNr, neg(X), mt(Num1, Num2)]|Next], List):-find([Num1, imp(X, Y), _], List),
                                                                    find([Num2, neg(Y), _], List),
                                                                    append(List, [[LineNr, X, neg(X), mt(Num1, Num2)]], NewList),!,
                                                                    validproof(Prems, Goal, Next, NewList).
%OREL
validproof(Prems, Goal, [[LineNr, X, orel(Num1, Num2, Num3, Num4, Num5)]|Next], List):-find([Num1, or(A, B), _], List),
                                                                                    find([Num2, A, assumption], List),
                                                                                    find([Num4, B, assumption], List),
                                                                                    find([Num3, X, _], List),
                                                                                    find([Num5, X, _], List),
                                                                                    append(List, [[LineNr, X, orel(Num1, Num2, Num3, Num4, Num5)]], NewList),!,
                                                                                    validproof(Prems, Goal, Next, NewList).


%PBC
validproof(Prems, Goal, [[LineNr, X, pbc(Num1, Num2)]|Next], List):-find([Num1, neg(X), _], List),
                                                                find([Num2, cont, _], List),
                                                                append(List, [[LineNr, X, pbc(Num1, Num2)]], NewList),!,
                                                                validproof(Prems, Goal, Next, NewList).

%NEGNEGINT
validproof(Prems, Goal, [[LineNr, neg(neg(X)), negnegint(Num)]|Next], List):-find([Num, X, _], List),
                                                                        append(List, [[LineNr, neg(neg(X)), negnegint(Num)]], NewList),!,
                                                                        validproof(Prems, Goal, Next, NewList).
