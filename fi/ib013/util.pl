:- module(util, [
	test_input/1,
	test_input2/1,
	sequence_to_edgelist/2,
	split_events/4,
	quadruples_to_events/2,
	table_lookup/3,
	table_update/4,
	vertices/3,
	edges_to_ugraph/2,
	count_degrees/3,
	even/1,
	connected/1,
	filter/3,
	partition/4,
	multidelete/3,
	split_packedevents/4,
	packedevents_to_edges/2,
	apply_packedevent_to_edges/3,
	quadruples_to_packedevents/2,
	max/3
]).

:- use_module(library(lists)).   % ruzne funkce pro seznamy
:- use_module(library(samsort)). % razeni podle dodaneho predikatu
:- use_module(library(ugraphs)). % knihovna pro praci s grafy

test_input(G) :-
	G = [
		[a-b, 0, 2],
		[a-e, 1, 7],
		[b-c, 0, 2],
		[c-d, 2, 3],
		[c-e, 1, 3],
		[b-d, 0, 4],
		[d-e, 1, 4],
		[b-e, 1, 2],
		[a-x, 3, 6],
		[x-y, 6, 7],
		[y-z, 6, 8],
		[z-x, 7, 8]

		%,[d-u, 1, 3] %odkomentovanim techto radek bude graf v okamziku 2 eulerovsky
		%,[c-u, 1, 3]

		%,[v-x, 4, 4]
		%,[v-b, 4, 4]
	].

test_input2(G) :-
	G = [
		[a-b, 1, 15],
		[b-c, 1, 5],
		[a-c, 1, 10],
		[c-d, 5, 15],
		[b-d, 5, 10],
		[a-d, 10, 15],
		[b-c, 10, 15]
	].

% Prevede (serazeny) seznam udalosti na seznam hran, ktery vznikne
% po provedeni techto udalosti.
% e.g. sequence_to_edgelist([add(a-b,1),add(b-c,2),del(a-b,3)],[b-c]).
sequence_to_edgelist(Events, Result) :- sequence_to_edgelist(Events, [], Result).
sequence_to_edgelist([], G, G).
sequence_to_edgelist([add(X-Y, _) | Tail], CurGraph, Result) :-
	sequence_to_edgelist(Tail, [X-Y|CurGraph], Result).
sequence_to_edgelist([del(X-Y, _) | Tail], CurGraph, Result) :-
	delete(CurGraph, X-Y, NewGraph),
	sequence_to_edgelist(Tail, NewGraph, Result).

% Vezme seznam (serazenych) udalosti a rozdeli je podle hodnoty Time
% na seznam udalosti co se staly pred Time a co se staly po Time.
% Pokud se nejaka udalost stane v Time a je to pridani hrany, je
% to jako by se stala predtim, pokud je to del, je to jako potom.
split_events([], _, [], []).
split_events([add(X-Y,Time) | T], Time, [add(X-Y,Time) | NPre], NPost) :-
	!,
	split_events(T, Time, NPre, NPost).
split_events([del(X-Y,Time) | T], Time, NPre, [del(X-Y,Time)|NPost]) :-
	!,
	split_events(T, Time, NPre, NPost).
split_events([Ev|T], Time, [], [Ev,T]) :-
	arg(2, Ev, EvTime),
	EvTime > Time,
	!.
split_events([H|T], Time, [H|NPre], NPost) :-
	split_events(T, Time, NPre, NPost).

% Prevede seznam ctveric (tak jak je popsany v predbezne zprave) na
% serazeny seznam udalosti add(Vrchol-Vrchol, Cas), del(Vrchol-Vrchol, Cas).
quadruples_to_events(G, Seq) :-
	to_unsorted_events(G, Events),
	samsort(before, Events, Seq).

to_unsorted_events([], []).
to_unsorted_events([[A-B, Start, End] | Tail], [add(A-B, Start), del(A-B, End) | NTail]) :-
	to_unsorted_events(Tail,NTail).

shift_deletions([], []).
shift_deletions([add(E, T)|Tail], [add(E,T)|NTail]) :- shift_deletions(Tail, NTail).
shift_deletions([del(E, T)|Tail], [del(E,T1)|NTail]) :-
	T1 is T + 1,
	shift_deletions(Tail, NTail).

% porovnani druheho argumentu obou termu.
before(T1, T2) :-
	arg(2, T1, Val1),
	arg(2, T2, Val2),
	Val1 < Val2.

% table_lookup(+Table, +Key, -Value)
% V tabulce dvojic Table vyhleda hodnotu klice Key.
table_lookup([K-V|_], K, V) :- !.
table_lookup([_|T], K, V) :- table_lookup(T,K,V).

% table_update(+Table, +Key, +NewValue, -NewTable).
% Nahradi hodnotu klice Key hodnotou NewValue a vrati takto zmenenou tabulku.
table_update([K-_ | T], K, NV, [K-NV | T]) :- !.
table_update([H | T], K, NV, [H | NT]) :-
	table_update(T, K, NV, NT).

% vertices(+InitEdges, +Seq, -VerticeList)
% Pro zadany seznam hran a posloupnost udalosti (jedno z toho muze byt prazdne)
% vrati seznam unikatnich vrcholu.
vertices(InitEdges, Seq, VerticeList) :-
	seq_strip_times(Seq, SeqEdges),
	append(InitEdges, SeqEdges, UnsortedEdges),
	break_edges(UnsortedEdges, UnsortedVertices),
	remove_dups(UnsortedVertices, VerticeList).

break_edges([], []).
break_edges([A-B | T], [A, B | NT]) :- break_edges(T,NT).

seq_strip_times([],[]).
seq_strip_times([add(A-B, _) | T], [A-B | NT]) :- seq_strip_times(T, NT).
seq_strip_times([del(A-B, _) | T], [A-B | NT]) :- seq_strip_times(T, NT).

%%% po nahrani na web %%%

% prevede seznam hran na ugraph tak jak je popsany v library(ugraphs)
edges_to_ugraph(Edges, Ugraph) :-
	vertices_edges_to_ugraph([], Edges, Dgraph),
	symmetric_closure(Dgraph, Ugraph).

%symmetrify(Edges, SymmEdges) :-
%	symm(Edges, E),
%	remove_dups(E, SymmEdges).
%
%symm([],[]).
%symm([X-Y | T], [X-Y, Y-X | NT]) :-
%	symm(T, NT).

% count_degrees(+Vertices, +Edges, -DegreeTable)
% Pro dany seznam vrcholu a seznam hran spocita stupne vrcholu
% do tabulky [vrchol-stupen].
count_degrees([], _, []).
count_degrees([V|T], Edges, [V-Num | NT]) :- 
	count_degree(V, Edges, Num),
	count_degrees(T, Edges, NT).

count_degree(_, [], 0).
count_degree(V, [X-Y | T], N) :-
	V \= X,
	V \= Y,
	!,
	count_degree(V, T, N).
count_degree(V, [_ | T], N) :-
	count_degree(V, T, N1),
	N is N1 + 1.

even(Number) :- 0 is Number mod 2.

% connected(+Edges).
% Uspeje, pokud mnozina hran tvori souvisly graf.
connected([]).
connected(Edges) :-
	Edges = [V-_ | _],
	edges_to_ugraph(Edges, UGraph),
	reachable(V, UGraph, Reachable),
	vertices(Edges, [], Vertices),
	sort(Reachable, SortedReachable),
	sort(Vertices, SortedVertices),
	SortedReachable = SortedVertices.

% filter a partition - delaji to same co v haskellu
filter(_, [], []).
filter(Pred, [Head | Tail], [Head | Filtered]) :-
	call(Pred, Head),
	!,
	filter(Pred, Tail, Filtered).
filter(Pred, [_ | Tail], Filtered) :-
	filter(Pred, Tail, Filtered).

partition(_, [], [], []).
partition(Pred, [H|T], [H|A], B) :-
	call(Pred, H),
	!,
	partition(Pred, T, A, B).
partition(Pred, [H|T], A, [H|B]) :-
	partition(Pred, T, A, B).

% multidelete(List, KillList, Residue)
% ze seznamu List odstrani vsechny prvky ktere jsou v seznamu KillList
multidelete(List, [], List).
multidelete(List, [Kill|Rest], Residue) :-
	delete(List, Kill, Killed),
	multidelete(Killed, Rest, Residue).

%%% "packed_events"
%%% Dalsi datovy format - tentokrat seznam udalosti tvaru
%%% ev(Time, AddEdges, DelEdges), Time je ces, AddEdges seznam
%%% hran ktere byly pridany, DelEdges seznam hran ktere byly odebrany

quadruples_to_packedevents(G, PackedSeq) :-
	to_unsorted_events(G, Seq),
	shift_deletions(Seq, ShiftedSeq),
	pack(ShiftedSeq, UnsortedPackedSeq),
	samsort(packed_before, UnsortedPackedSeq, PackedSeq).
	%nl, print('packed sequence: '), print(PackedSeq).

packed_before(ev(T1, _, _), ev(T2, _, _)) :- T1 < T2.

pack([], []).
pack([Head | Tail], Result) :-
	arg(2, Head, Time),
	pack_edges(Time, [Head|Tail], [], [], [], AddEdges, DelEdges, Rest),
	pack(Rest, NResult),
	Result = [ ev(Time, AddEdges, DelEdges) | NResult ].

pack_edges(_, [], AddEdges, DelEdges, Rest, AddEdges, DelEdges, Rest).
pack_edges(Time, [Head | Tail], AccAddEdges, AccDelEdges, AccRest, AddEdges, DelEdges, Rest) :-
	arg(2, Head, Time),
	!,
	(
		Head = add(Edge, Time),
		AccAdd1 = [Edge|AccAddEdges],
		AccDel1 = AccDelEdges
	;
		Head = del(Edge, Time),
		AccAdd1 = AccAddEdges,
		AccDel1 = [Edge|AccDelEdges]
	),
	pack_edges(Time, Tail, AccAdd1, AccDel1, AccRest, AddEdges, DelEdges, Rest).
pack_edges(Time, [Head | Tail], AccAddEdges, AccDelEdges, AccRest, AddEdges, DelEdges, Rest) :-
	AccRest1 = [Head | AccRest],
	pack_edges(Time, Tail, AccAddEdges, AccDelEdges, AccRest1, AddEdges, DelEdges, Rest).

% Dela to same co split_events, ale nad 'packedevents'.
split_packedevents([], _, [], []).
%split_packedevents([ev(Time, AddEdges, DelEdges) | T], Time, [ev(Time,AddEdges,[])|NPre], [ev(Time,[],DelEdges)|NPost]) :-
%	!,
%	split_packedevents(T, Time, NPre, NPost).
split_packedevents([Ev|T], Time, [], [Ev|T]) :-
	arg(1, Ev, EvTime),
	EvTime > Time,
	!.
split_packedevents([H|T], Time, [H|NPre], NPost) :-
	split_packedevents(T, Time, NPre, NPost).

% apply_packedevent_to_edges(+Graph, +PackedEvent, -NewGraph).
% Aplikuje udalost PackedEvent na seznam hran Graph.
apply_packedevent_to_edges(Edges, ev(Time, AddEdges, DelEdges), NewEdges) :-
	multidelete(Edges, DelEdges, NewGraph1),
	append(NewGraph1, AddEdges, NewEdges).
	%nl, nl, print('time: '), print(Time), print(' new graph: '), print(NewEdges).


% Dela to same co sequence_to_edgelist, ale nad 'packedevents'.
packedevents_to_edges(Events, Result) :- packedevents_to_edges(Events, [], Result).
packedevents_to_edges([], G, G).
packedevents_to_edges([Event | Tail], CurGraph, Result) :-
	apply_packedevent_to_edges(CurGraph, Event, NewGraph),
	packedevents_to_edges(Tail, NewGraph, Result).

max(A, B, A) :- A >= B, !.
max(A, B, B) :- B > A.

