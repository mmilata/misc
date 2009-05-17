%:- module(longest_cycle, [longest_cycle/2, longest_cycle/3, longest_cycle/4]).

:- use_module(util).
:- use_module(library(lists)).

maxcycle(Graph, MaxCycle) :-
	vertices(Graph, [], Vertices),
	maxcycle(Vertices, [], Graph, [], MaxCycle).

maxcycle([], _Banned, _Graph, MaxCycle, MaxCycle).
maxcycle([V|Rest], Banned, Graph, Acc, MaxCycle) :-
	maxcycle_from_vertex([V], Graph, Banned, LocalCycle),
	length(Acc, AccLength),
	length(LocalCycle, LocalLength),
	if(LocalLength > AccLength, NewCycle = LocalCycle, NewCycle = Acc),
	maxcycle(Rest, [V|Banned], Graph, NewCycle, MaxCycle).

%??????????????????
% nechceme cykly delky 2
%maxcycle_from_vertex([A, B, A], _Graph, _Banned, _Cycle) :- fail.


% nasli jsme cyklus
maxcycle_from_vertex([CurVert | Stack], _Graph, _Banned, Cycle) :-
	last(_, CurVert, Stack),
	length(Stack, SLen),
	SLen > 2, %cykly typu a-b-a nas nezajimaji
	!,
	%nl, print('cycle: '), print([CurVert | Stack]),
	Cycle = [CurVert | Stack].

% jsme ve vrcholu ve kterem uz jsme byli
maxcycle_from_vertex([CurVert | Stack], _Graph, _Banned, Cycle) :-
	memberchk(CurVert, Stack),
	!,
	Cycle = [].

% nejsme v cyklu - rekurze, secist
maxcycle_from_vertex([CurVert | Stack], Graph, Banned, MaxCycle) :-
	edges_neighbors(Graph, CurVert, Neighbors),
	multidelete(Neighbors, Banned, Neighs1),
	walk_neighbors(Neighs1, [CurVert | Stack], Graph, Banned, [], MaxCycle).

walk_neighbors([], _, _, _, MaxCycle, MaxCycle).
walk_neighbors([Neigh|Rest], Stack, Graph, Banned, AccCycle, MaxCycle) :-
	maxcycle_from_vertex([Neigh|Stack], Graph, Banned, NeighCycle),
	length(AccCycle, AccLength),
	length(NeighCycle, NeighLength),
	if(NeighLength > AccLength, Acc1 = NeighCycle, Acc1 = AccCycle),
	walk_neighbors(Rest, Stack, Graph, Banned, Acc1, MaxCycle).
