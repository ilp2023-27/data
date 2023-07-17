%%%%%%%%%%%%%%%%%% MODES & BIAS
#constant(node_id, 1..7).
#constant(op, next).
#constant(op, until).
#constant(op, eventually).
#constant(op, always).
#constant(op, and).
#constant(op, neg).
#constant(op, or).
#constant(op, implies).
#modeh( edge(const(node_id), const(node_id)) ).
#modeh( label(const(node_id), const(op)) ).
#modeh( label(const(node_id), const(atom)) ).

% Acyclic graphs
#bias(":- head(edge(X,Y)), Y <= X.").

%%%%%%%%%%%%%%%%%%%

#pos(bias_eid,{},{},{
% A node is a term in edge/2 or something that is labeled via label/2
node(X) :- label(X,_).
node(X) :- edge(_,X).
node(X) :- edge(X,_).

label(1,always).

% If you use identifier X+1, you must be using X too
node(X) :- node(X+1), X >= 1.

% The DAG must be connected
reach(1).
reach(T) :- edge(R,T), reach(R).
:- node(X), not reach(X).
:- node(X), not edge(_,X), X > 1.

% Bounded fan-out
:- node(X), 3 #count { Z: edge(X,Z) }.

% Exactly one label per node
:- node(X), not label(X,_).
:- label(X,A), label(X,B), A < B.

% Labels must match arity of the nodes
arity(X,0) :- node(X), not edge(X,_).
arity(X,2) :- node(X), edge(X,Y), edge(X,Y1), Y < Y1.
arity(X,1) :- node(X), not arity(X,0), not arity(X,2).

symbol(A,0) :- proposition(A).
symbol(next,1).
symbol(until,2).
symbol(eventually,1).
symbol(always,1).

symbol(neg,1).
symbol(and,2).
symbol(or,2).
symbol(implies,2).

:- arity(X,N), label(X,Y), not symbol(Y,N).

%%%%%%%%%%% BFS PRUNE (?)
id(1,(0,0)).
id(V,(U,V*V+U)) :- edge(U,V).
%:- id(I,RI), id(J,RJ), I < J, RI >= RJ.
%:- id(I,RI), id(J,RJ), I > J, RI <= RJ.
:- id(I,RI), id(I+1, RJ), RI >= RJ.
:- id(I+1,RI), id(I,RJ), RI <= RJ.
}).

%%%%%%%%%%%%%%%%%% BACKGROUND KNOWLEDGE FORMULA EVALUATION

order(X, LHS, RHS) :- edge(X,LHS), edge(X,RHS), LHS < RHS.



holds(T, X) :- label(X, A), trace(T, A).



holds(T, X) :- label(X, next), edge(X, Y), holds(T+1, Y), not last(T), trace(T).

holds(T, X) :- label(X, until), order(X,LHS,RHS), holds(T, RHS), trace(T).
holds(T, X) :- label(X, until), order(X,LHS,RHS), holds(T, LHS), holds(T+1, X), trace(T).

holds(T, X) :- label(X, and), order(X,A,B), holds(T, A), holds(T, B), trace(T).
holds(T, X) :- label(X, or), edge(X, A), holds(T, A), trace(T).
holds(T, X) :- label(X, neg), edge(X, Y), not holds(T, Y), trace(T).
holds(T, X) :- label(X,implies), order(X,LHS,RHS), holds(T,RHS), holds(T,LHS).
holds(T, X) :- label(X,implies), order(X,LHS,RHS), not holds(T,LHS), trace(T).

holds(T, X) :- label(X, eventually), edge(X,Y), holds(T,Y).
holds(T, X) :- label(X, eventually), holds(T+1, X), trace(T).

holds(T, X) :- label(X, always), edge(X, Y), holds(T, Y), last(T).
holds(T, X) :- label(X, always), edge(X, Y), holds(T, Y), holds(T+1, X), trace(T).

last(T) :- trace(T), not trace(T+1).
sat :- holds(0,1).
unsat :- not sat.

unsat :- label(1, always), not holds(T, 1), trace(T).

:- sat, unsat.
