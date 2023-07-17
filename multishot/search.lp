%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% BASE PROGRAM
#program base.
symbol(and, 2).
symbol(or, 2).
symbol(neg, 1).
symbol(until, 2).
symbol(eventually, 1).
symbol(always, 1).
symbol(next, 1).
symbol(implies,2).
symbol(A,0) :- proposition(A).
last(TID,T) :- trace(TID,T), not trace(TID,T+1).
parent(1,(0,0)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% TREE SEARCH
#program search(t).
node(t).
pair(X,t) :- node(X), node(t), X < t.
1 { edge(X,t): pair(X,t) } 1 :- node(t), t > 1.
:- n { edge(X,Y) }.
:- node(X), 3 { edge(X,Y) }.

%%%%%%% BFS PRUNING
parent(t, (U,t*t+U)) :- bfs_pruning, edge(U,t).
:- parent(I,RI), parent(J,RJ), I < J, RI >= RJ, bfs_pruning.
:- parent(I,RI), parent(J,RJ), I >= J, RI < RJ, bfs_pruning.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FORMULA LABELING
#program eval(n).
#external shot(n).
label(n,1,always).

:- shot(n),     holds(n,TID,0,1), neg(TID).
:- shot(n), not holds(n,TID,0,1), pos(TID).

:- shot(n), label(n,1,always), not holds(n,TID,_,1), pos(TID).

arity(n,X,C) :- node(X), C = #count{Y: edge(X,Y)}, shot(n).

1 { label(n,X,A): proposition(A) } 1 :- shot(n), node(X), arity(n,X,0).
:- shot(n), not label(n, 1, always).

1 { label(n,X,L): symbol(L,C) } 1 :- shot(n), node(X), arity(n,X,C), C > 0.

order(n,X,LHS,RHS) :- shot(n), node(X), edge(X,LHS), edge(X,RHS), LHS < RHS.

% Atomic propositions
% holds(T, X) :- label(X, A), trace(T, A).
holds(n, TID, T, X) :- label(n,X,A), trace(TID, T, A), shot(n).

%  holds(T, X) :- label(X, next), edge(X, Y), holds(T+1, Y), not last(T), trace(T).
% Next
holds(n, TID, T, X) :- 
	label(n,X,next), 
	edge(X,Y), 
	holds(n, TID, T+1, Y),
	not last(TID,T),
	trace(TID,T),
	shot(n).

% holds(T, X) :- label(X, until), order(X,LHS,RHS), holds(T, RHS), trace(T).
% holds(T, X) :- label(X, until), order(X,LHS,RHS), holds(T, LHS), holds(T+1, X), trace(T).
% Until
holds(n, TID, T, X) :-
	label(n,X,until),
	order(n,X,LHS,RHS),
	holds(n,TID,T,RHS),
	trace(TID,T),
	shot(n).

holds(n, TID, T, X) :-
	label(n,X,until),
	order(n,X,LHS,RHS),
	holds(n,TID,T+1,X),
	holds(n,TID,T,LHS),
	trace(TID,T),
	shot(n).

% holds(T, X) :- label(X, eventually), edge(X,Y), holds(T,Y).
% holds(T, X) :- label(X, eventually), holds(T+1, X), trace(T).
% Eventually
holds(n, TID, T, X) :-
	label(n, X, eventually),
	edge(X,Y),
	holds(n, TID, T, Y),
	shot(n).

holds(n, TID, T, X) :-
	label(n, X, eventually),
	holds(n, TID, T+1, X),
	shot(n),
	trace(TID,T).

% Always
% holds(T, X) :- label(X, always), edge(X, Y), holds(T, Y), last(T).
% holds(T, X) :- label(X, always), edge(X, Y), holds(T, Y), holds(T+1, X), trace(T).
holds(n, TID, T, X) :-
	label(n, X, always),
	edge(X,Y),
	last(TID,T),
	holds(n, TID, T, Y),
	shot(n).

holds(n, TID, T, X) :-
	label(n, X, always),
	edge(X,Y),
	holds(n, TID, T+1, X),
	holds(n, TID, T, Y),
	shot(n).

% And
holds(n, TID, T, X) :-
	label(n,X,and),
	edge(X,Y1), 
	edge(X,Y2), 
	Y1 < Y2, 
	holds(n, TID, T, Y1), 
	holds(n, TID, T, Y2), 
	shot(n).

% Or
holds(n, TID, T, X) :- 
	label(n,X,or), 
	edge(X,Y), 
	holds(n,TID,T,Y), 
	shot(n).

% Neg
holds(n, TID, T, X) :- 
	label(n,X,neg), 
	edge(X,Y), 
	not holds(n,TID,T,Y), 
	trace(TID,T), 
	shot(n).

% Implies
holds(n, TID, T, X) :- 
	label(n,X,implies), 
	order(n,X,LHS,RHS), 
	holds(n,TID,T,RHS), 
	shot(n).

holds(n, TID, T, X) :- 
	label(n,X,implies), 
	order(n,X,LHS,RHS), 
	not holds(n,TID,T,LHS), 
	trace(TID,T), 
	shot(n).

#show.
#show edge(X,Y): edge(X,Y).
#show label(X,A): shot(n), label(n,X,A).
