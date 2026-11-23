% PrologScript's core, stated in Prolog: the scene (shapes, groups, layers), hit testing and
% bounds, hierarchical menus, painting (lines, flood fill, brush dots) and pointers.
%
% This is a model of its own, not a translation: a scene is sc(Layers, Active, Selected), each
% layer(Id, Name, Shown, Locked, Items) holding trees of s(Id, Kind, G, Fill, Width) and
% g(Id, Items), bottom first. proofs/ios.pl checks that on the 200 recorded inputs it gives the
% outputs the JavaScript gave; proofs/theorems.pl proves properties of it by exhaustion.
% Values are JSON as SWI-Prolog reads it: strings, numbers, true/false/null, dicts, lists.

:- module(ps_spec, [spec/3, apply_op/3, empty/1, outline/2, well_formed/1, hit/5, line_points/5,
                    fill_grid/5, menu_key/4, menu_choose/3, usable/1, sc_bounds/3, dot_grid/7, cursor/2]).
:- use_module(library(lists)).
:- use_module(library(apply)).

% ------------------------------------------------------------------ the scene

empty(sc([layer("layer1", "Layer 1", true, false, [])], "layer1", [])).

kind(K) :- memberchk(K, ["rect", "ellipse", "line", "poly", "path", "text"]).

% a name: a small letter, then letters, digits and _ (40 at most)
id_ok(Id) :- string(Id), string_chars(Id, [C|Cs]), length([C|Cs], L), L =< 40, small(C), maplist(word_char, Cs).
small(C) :- char_code(C, K), K >= 0'a, K =< 0'z.
word_char(C) :- char_code(C, K), ( K >= 0'a, K =< 0'z ; K >= 0'A, K =< 0'Z ; K >= 0'0, K =< 0'9 ; K =:= 0'_ ), !.

err(Fmt, Args) :- format(string(M), Fmt, Args), throw(ps(M)).

node_id(s(Id, _, _, _, _), Id).
node_id(g(Id, _), Id).

% every node in a list of trees, depth first
nodes_in([], []).
nodes_in([N|Ns], [N|Out]) :- ( N = g(_, Kids) -> nodes_in(Kids, K1) ; K1 = [] ), nodes_in(Ns, Rest), append(K1, Rest, Out).
all_nodes(sc(Ls, _, _), Ns) :- findall(N, ( member(layer(_, _, _, _, Items), Ls), nodes_in(Items, NN), member(N, NN) ), Ns).
has_node(Sc, Id) :- all_nodes(Sc, Ns), member(N, Ns), node_id(N, Id), !.
has_layer(sc(Ls, _, _), Id) :- memberchk(layer(Id, _, _, _, _), Ls).

% where a node is: place(Layer, Parent), Parent = none (the layer's list) or a group's id
place_of(sc(Ls, _, _), Id, place(L, P)) :-
    member(layer(L, _, _, _, Items), Ls), place_in(Items, none, Id, P), !.
place_in(Items, P, Id, P) :- member(N, Items), node_id(N, Id), !.
place_in(Items, _, Id, P) :- member(g(G, Kids), Items), place_in(Kids, G, Id, P), !.

layer_locked(sc(Ls, _, _), L) :- memberchk(layer(L, _, _, true, _), Ls).

% the list a place holds, and a scene with that list replaced
list_at(sc(Ls, _, _), place(L, none), Items) :- !, memberchk(layer(L, _, _, _, Items), Ls).
list_at(Sc, place(_, G), Items) :- all_nodes(Sc, Ns), memberchk(g(G, Items), Ns).
set_list(sc(Ls0, A, S), place(L, none), Items, sc(Ls, A, S)) :- !,
    maplist(set_layer_items(L, Items), Ls0, Ls).
set_list(sc(Ls0, A, S), place(_, G), Items, sc(Ls, A, S)) :-
    maplist(set_group_in_layer(G, Items), Ls0, Ls).
set_layer_items(L, Items, layer(L, N, Sh, Lk, _), layer(L, N, Sh, Lk, Items)) :- !.
set_layer_items(_, _, Layer, Layer).
set_group_in_layer(G, Items, layer(L, N, Sh, Lk, Is0), layer(L, N, Sh, Lk, Is)) :- maplist(set_group(G, Items), Is0, Is).
set_group(G, Items, g(G, _), g(G, Items)) :- !.
set_group(G, Items, g(H, K0), g(H, K)) :- !, maplist(set_group(G, Items), K0, K).
set_group(_, _, N, N).

% a node, found anywhere
node_of(Sc, Id, N) :- all_nodes(Sc, Ns), member(N, Ns), node_id(N, Id), !.
% every id in a node, itself included
within(N, Ids) :- nodes_in([N], Ns), maplist(node_id, Ns, Ids).

remove_ids(Ids, S0, S) :- exclude({Ids}/[X]>>memberchk(X, Ids), S0, S).

% ---- the operations: apply_op(Op, Scene0, Scene), or throw ps(Message)
apply_op(["add", Id, Kind, G, St], Sc0, Sc) :-
    ( id_ok(Id) -> true ; err("~w: a name starts with a small letter", [Id]) ),
    ( ( has_node(Sc0, Id) ; has_layer(Sc0, Id) ) -> err("~w is already there", [Id]) ; true ),
    ( kind(Kind) -> true ; err("~w isn't a shape", [Kind]) ),
    Sc0 = sc(Ls, Active, _),
    memberchk(layer(Active, AName, _, ALocked, Items), Ls),
    ( ALocked == true -> err("~w is locked", [AName]) ; true ),
    ( geometry(Kind, G) -> true ; err("~w: not a shape I can draw", [Kind]) ),
    ( get_dict(fill, St, F) -> true ; F = "none" ),
    ( get_dict(width, St, W) -> true ; W = 2 ),
    append(Items, [s(Id, Kind, G, F, W)], Items1),
    set_list(Sc0, place(Active, none), Items1, Sc).
apply_op(["remove", Id], Sc0, sc(Ls, A, Sel)) :-
    ( place_of(Sc0, Id, Pl) -> true ; err("~w isn't there", [Id]) ),
    Pl = place(L, _),
    ( layer_locked(Sc0, L) -> err("~w is on a locked layer", [Id]) ; true ),
    node_of(Sc0, Id, N), within(N, Gone),
    list_at(Sc0, Pl, Items), exclude({Id}/[X]>>node_id(X, Id), Items, Items1),
    set_list(Sc0, Pl, Items1, sc(Ls, A, S0)),
    remove_ids(Gone, S0, Sel).
apply_op(["move", Id, DX, DY], Sc0, Sc) :-
    ( number(DX), number(DY) -> true ; err("move: by numbers", []) ),
    ( place_of(Sc0, Id, place(L, _)) -> true ; err("~w isn't there", [Id]) ),
    ( layer_locked(Sc0, L) -> err("~w is on a locked layer", [Id]) ; true ),
    node_of(Sc0, Id, N), within(N, Ids),
    map_shapes(shifted(Ids, DX, DY), Sc0, Sc).
apply_op(["group", Ids, Gid], Sc0, Sc) :-
    ( id_ok(Gid) -> true ; err("~w: a name starts with a small letter", [Gid]) ),
    ( has_node(Sc0, Gid) -> err("~w is already there", [Gid]) ; true ),
    ( is_list(Ids), Ids \== [] -> true ; err("group: which items?", []) ),
    ( sort(Ids, U), length(U, N1), length(Ids, N1) -> true ; err("group: an item is named twice", []) ),
    maplist(place_or_missing(Sc0), Ids, Places),
    Places = [P1|_],
    ( maplist(==(P1), Places) -> true ; err("group: the items must be side by side (in the same layer or group)", []) ),
    P1 = place(L, _),
    ( layer_locked(Sc0, L) -> err("group: the layer is locked", []) ; true ),
    list_at(Sc0, P1, List),
    include({Ids}/[X]>>( node_id(X, I), memberchk(I, Ids) ), List, Members),
    findall(K, ( nth0(K, List, X), node_id(X, I), memberchk(I, Ids) ), Ks), max_list(Ks, Top),
    length(Members, M), At is Top - (M - 1),
    exclude({Ids}/[X]>>( node_id(X, I), memberchk(I, Ids) ), List, Rest),
    insert_at(At, g(Gid, Members), Rest, List1),
    set_list(Sc0, P1, List1, sc(Ls, A, S0)),
    remove_ids(Ids, S0, S),
    Sc = sc(Ls, A, S).
apply_op(["ungroup", Gid], Sc0, Sc) :-
    ( node_of(Sc0, Gid, N) -> true ; err("~w isn't there", [Gid]) ),
    ( N = g(_, Kids) -> true ; err("~w isn't a group", [Gid]) ),
    place_of(Sc0, Gid, Pl), Pl = place(L, _),
    ( layer_locked(Sc0, L) -> err("ungroup: the layer is locked", []) ; true ),
    list_at(Sc0, Pl, List),
    append(Before, [g(Gid, _)|After], List), append(Before, Kids, B1), append(B1, After, List1),
    set_list(Sc0, Pl, List1, sc(Ls, A, S0)),
    remove_ids([Gid], S0, S), Sc = sc(Ls, A, S).
apply_op(["restack", Id, How], Sc0, Sc) :-
    ( place_of(Sc0, Id, Pl) -> true ; err("~w isn't there", [Id]) ),
    Pl = place(L, _),
    ( layer_locked(Sc0, L) -> err("~w is on a locked layer", [Id]) ; true ),
    list_at(Sc0, Pl, List),
    nth0(I, List, X), node_id(X, Id), !,
    length(List, Len), Last is Len - 1,
    ( How == "raise" -> J is min(Last, I + 1) ; How == "lower" -> J is max(0, I - 1)
    ; How == "front" -> J = Last ; How == "back" -> J = 0 ; err("~w: raise, lower, front or back", [How]) ),
    nth0(I, List, X, Rest), nth0(J, List1, X, Rest),
    set_list(Sc0, Pl, List1, Sc).
apply_op(["addLayer", Id, Name], Sc0, sc(Ls1, Id, S)) :-
    ( id_ok(Id) -> true ; err("~w: a name starts with a small letter", [Id]) ),
    ( ( has_node(Sc0, Id) ; has_layer(Sc0, Id) ) -> err("~w is already there", [Id]) ; true ),
    Sc0 = sc(Ls, _, S),
    name_text(Name, Id, N),
    append(Ls, [layer(Id, N, true, false, [])], Ls1).
apply_op(["useLayer", Id], sc(Ls, A0, S), sc(Ls, A, S)) :-
    ( has_layer(sc(Ls, A0, S), Id) -> A = Id ; err("~w isn't a layer", [Id]) ).
apply_op(["setLayer", Id, Key, V], sc(Ls0, A, S0), sc(Ls, A, S)) :-
    ( memberchk(Key, ["shown", "locked"]), memberchk(V, [true, false]) -> true ; err("a layer is shown or locked: true or false", []) ),
    ( memberchk(layer(Id, _, _, _, _), Ls0) -> true ; err("~w isn't a layer", [Id]) ),
    maplist(set_flag(Id, Key, V), Ls0, Ls),
    (   ( Key == "shown", V == false ; Key == "locked", V == true )
    ->  exclude({Ls, A, S0, Id}/[X]>>layer_of(sc(Ls, A, S0), X, Id), S0, S)
    ;   S = S0 ).
apply_op(["moveLayer", Id, How], sc(Ls0, A, S), sc(Ls, A, S)) :-
    ( nth0(I, Ls0, layer(Id, N, Sh, Lk, It)) -> true ; err("~w isn't a layer", [Id]) ),
    length(Ls0, Len), Last is Len - 1,
    ( How == "raise" -> J is min(Last, I + 1) ; How == "lower" -> J is max(0, I - 1) ; err("~w: raise or lower", [How]) ),
    nth0(I, Ls0, _, Rest), nth0(J, Ls, layer(Id, N, Sh, Lk, It), Rest).
apply_op(["toLayer", Id, Lid], Sc0, Sc) :-
    ( place_of(Sc0, Id, place(From, P)) -> true ; err("~w isn't there", [Id]) ),
    ( P == none -> true ; err("~w is inside ~w: ungroup it first", [Id, P]) ),
    ( has_layer(Sc0, Lid) -> true ; err("~w isn't a layer", [Lid]) ),
    ( ( layer_locked(Sc0, Lid) ; layer_locked(Sc0, From) ) -> err("a locked layer", []) ; true ),
    (   From == Lid -> Sc = Sc0
    ;   list_at(Sc0, place(From, none), FL), append(B, [N|Af], FL), node_id(N, Id), !, append(B, Af, FL1),
        set_list(Sc0, place(From, none), FL1, Sc1),
        list_at(Sc1, place(Lid, none), TL), append(TL, [N], TL1),
        set_list(Sc1, place(Lid, none), TL1, Sc) ).
apply_op(["select", Ids], sc(Ls, A, _), sc(Ls, A, S)) :-
    forall(member(I, Ids), ( has_node(sc(Ls, A, []), I) -> true ; err("~w isn't there", [I]) )),
    dedupe(Ids, S).

place_or_missing(Sc, Id, P) :- ( place_of(Sc, Id, P) -> true ; err("~w isn't there", [Id]) ).
layer_of(Sc, Id, L) :- place_of(Sc, Id, place(L, _)).
set_flag(Id, "shown", V, layer(Id, N, _, Lk, It), layer(Id, N, V, Lk, It)) :- !.
set_flag(Id, "locked", V, layer(Id, N, Sh, _, It), layer(Id, N, Sh, V, It)) :- !.
set_flag(_, _, _, L, L).
name_text(Name, Id, N) :- ( string(Name) -> T = Name ; term_string(Name, T) ), string_length(T, Len), K is min(40, Len), sub_string(T, 0, K, _, T1), ( T1 == "" -> N = Id ; N = T1 ).
insert_at(I, X, L, L1) :- length(B, I), append(B, A, L), !, append(B, [X|A], L1).
dedupe([], []).
dedupe([X|Xs], [X|Ys]) :- exclude(==(X), Xs, Zs), dedupe(Zs, Ys).

% geometry each kind accepts
geometry("rect", [X, Y, W, H]) :- maplist(number, [X, Y, W, H]), W >= 0, H >= 0.
geometry("ellipse", [X, Y, W, H]) :- maplist(number, [X, Y, W, H]), W >= 0, H >= 0.
geometry("line", G) :- length(G, 4), maplist(number, G).
geometry("poly", Ps) :- points(Ps).
geometry("path", Ps) :- points(Ps).
geometry("text", [X, Y, S, T]) :- number(X), number(Y), number(S), S > 0, string(T).
points(Ps) :- is_list(Ps), length(Ps, N), N >= 2, forall(member(P, Ps), ( P = [A, B], number(A), number(B) )).

% change every shape (anywhere) with a predicate on s/5 terms
map_shapes(F, sc(Ls0, A, S), sc(Ls, A, S)) :- maplist(map_layer(F), Ls0, Ls).
map_layer(F, layer(L, N, Sh, Lk, I0), layer(L, N, Sh, Lk, I)) :- maplist(map_node(F), I0, I).
map_node(F, g(G, K0), g(G, K)) :- !, maplist(map_node(F), K0, K).
map_node(F, N0, N) :- call(F, N0, N).
shifted(Ids, DX, DY, s(Id, K, G0, F, W), s(Id, K, G, F, W)) :- memberchk(Id, Ids), !, shift(K, G0, DX, DY, G).
shifted(_, _, _, N, N).
shift(K, [X, Y, A, B], DX, DY, [X1, Y1, A, B]) :- memberchk(K, ["rect", "ellipse", "text"]), !, X1 is X + DX, Y1 is Y + DY.
shift("line", [X1, Y1, X2, Y2], DX, DY, [A1, B1, A2, B2]) :- !, A1 is X1 + DX, B1 is Y1 + DY, A2 is X2 + DX, B2 is Y2 + DY.
shift(_, Ps, DX, DY, Qs) :- maplist({DX, DY}/[[X, Y], [X1, Y1]]>>( X1 is X + DX, Y1 is Y + DY ), Ps, Qs).

% a script: the operations in turn, stopping at the first that throws
script(Ops, Out) :-
    empty(E),
    run_ops(Ops, 0, E, Sc, Err),
    describe(Sc, D),
    ( Err = none -> Out = D ; Err = err(At, M), put_dict(error, D, _{at: At, message: M}, Out) ).
run_ops([], _, Sc, Sc, none).
run_ops([Op|Ops], I, Sc0, Sc, Err) :-
    catch(( apply_op(Op, Sc0, Sc1), R = ok ), ps(M), R = err(I, M)),
    ( R = ok -> I1 is I + 1, run_ops(Ops, I1, Sc1, Sc, Err) ; Sc = Sc0, Err = R ).
build(Ops, Sc) :- empty(E), foldl([Op, S0, S]>>( catch(apply_op(Op, S0, S), ps(_), S = S0) ), Ops, E, Sc).

describe(Sc, _{outline: O, layers: Ls, active: A, selected: S, shapes: Sh}) :-
    Sc = sc(Layers, A, S),
    outline(Sc, O),
    findall([Id, N, Shw, Lk], member(layer(Id, N, Shw, Lk, _), Layers), Ls),
    all_nodes(Sc, Ns),
    findall(Id-[Id, K, G], member(s(Id, K, G, _, _), Ns), Pairs), keysort(Pairs, Sorted), pairs_values(Sorted, Sh).
outline(sc(Ls, _, _), O) :- findall([Id, IO], ( member(layer(Id, _, _, _, Items), Ls), maplist(node_outline, Items, IO) ), O).
node_outline(s(Id, _, _, _, _), Id).
node_outline(g(Id, Kids), [Id, KO]) :- maplist(node_outline, Kids, KO).

% well formed: every node once, selection only of nodes, the active layer there
well_formed(Sc) :-
    Sc = sc(Ls, A, S),
    all_nodes(Sc, Ns), maplist(node_id, Ns, Ids), msort(Ids, M), sort(Ids, M),
    findall(L, member(layer(L, _, _, _, _), Ls), LIds), sort(LIds, LS), length(LIds, NL), length(LS, NL),
    memberchk(A, LIds),
    forall(member(X, S), memberchk(X, Ids)).

% ------------------------------------------------------------------ looking

% the bounds of a node: [X, Y, W, H]
sc_bounds(Sc, Id, B) :- ( node_of(Sc, Id, N) -> node_bounds(N, B) ; err("~w isn't there", [Id]) ).
node_bounds(s(_, "rect", B, _, _), B) :- !.
node_bounds(s(_, "ellipse", [CX, CY, RX, RY], _, _), [X, Y, W, H]) :- !, X is CX - RX, Y is CY - RY, W is 2 * RX, H is 2 * RY.
node_bounds(s(_, "line", [X1, Y1, X2, Y2], _, _), [X, Y, W, H]) :- !, X is min(X1, X2), Y is min(Y1, Y2), W is abs(X2 - X1), H is abs(Y2 - Y1).
node_bounds(s(_, "text", [X, Y, S, T], _, _), [X, Y0, W, H]) :- !, Y0 is Y - S, string_length(T, L), W is round(L * S * 0.6), H is S * 1.25.
node_bounds(s(_, _, Ps, _, _), [X, Y, W, H]) :- !,
    findall(A, member([A, _], Ps), Xs), findall(B, member([_, B], Ps), Ys),
    min_list(Xs, X), max_list(Xs, X1), min_list(Ys, Y), max_list(Ys, Y1), W is X1 - X, H is Y1 - Y.
node_bounds(g(_, []), [0, 0, 0, 0]) :- !.
node_bounds(g(_, Kids), [X, Y, W, H]) :-
    maplist(node_bounds, Kids, Bs),
    findall(A, member([A, _, _, _], Bs), X0s), min_list(X0s, X),
    findall(B, member([_, B, _, _], Bs), Y0s), min_list(Y0s, Y),
    findall(R, ( member([A, _, W1, _], Bs), R is A + W1 ), Rs), max_list(Rs, XR),
    findall(R, ( member([_, B, _, H1], Bs), R is B + H1 ), Ds), max_list(Ds, YB),
    W is XR - X, H is YB - Y.

% does a shape cover a point? (its line, with slack; inside too when it's filled)
covers(s(_, K, G, Fill, Width), X, Y) :-
    Slack is max(4, Width / 2 + 3), S2 is Slack * Slack,
    ( Fill == "none" -> Filled = false ; Filled = true ),
    covers(K, G, Filled, Slack, S2, X, Y).
covers("rect", [RX, RY, W, H], true, _, _, X, Y) :- !, X >= RX, X =< RX + W, Y >= RY, Y =< RY + H.
covers("rect", [RX, RY, W, H], false, Sl, _, X, Y) :- !,
    X >= RX - Sl, X =< RX + W + Sl, Y >= RY - Sl, Y =< RY + H + Sl,
    \+ ( X > RX + Sl, X < RX + W - Sl, Y > RY + Sl, Y < RY + H - Sl ).
covers("ellipse", [CX, CY, RX, RY], F, Sl, _, X, Y) :- !,
    RX =\= 0, RY =\= 0,
    D is ((X - CX) / RX) ** 2 + ((Y - CY) / RY) ** 2,
    ( F == true -> D =< 1 ; R is sqrt(D), M is min(RX, RY), abs(R - 1) * M =< Sl ).
covers("line", [X1, Y1, X2, Y2], _, _, S2, X, Y) :- !, seg_dist2(X, Y, X1, Y1, X2, Y2, D), D =< S2.
covers("poly", Ps, F, _, S2, X, Y) :- !,
    (   F == true, in_poly(X, Y, Ps) -> true
    ;   last(Ps, L), [L|Ps] = Closed, near_segment(Closed, S2, X, Y) ).
covers("path", Ps, _, _, S2, X, Y) :- !, near_segment(Ps, S2, X, Y).
covers("text", G, _, _, _, X, Y) :- node_bounds(s(t, "text", G, none, 1), [BX, BY, BW, BH]), X >= BX, X =< BX + BW, Y >= BY, Y =< BY + BH.

near_segment([[X1, Y1], [X2, Y2]|Ps], S2, X, Y) :-
    (   seg_dist2(X, Y, X1, Y1, X2, Y2, D), D =< S2 -> true ; near_segment([[X2, Y2]|Ps], S2, X, Y) ).
seg_dist2(PX, PY, X1, Y1, X2, Y2, D) :-
    DX is X2 - X1, DY is Y2 - Y1, L is DX * DX + DY * DY,
    ( L =:= 0 -> T = 0 ; T0 is ((PX - X1) * DX + (PY - Y1) * DY) / L, T is max(0, min(1, T0)) ),
    QX is X1 + T * DX - PX, QY is Y1 + T * DY - PY, D is QX * QX + QY * QY.
% even-odd ray casting
in_poly(X, Y, Ps) :- last(Ps, Last), crossings([Last|Ps], X, Y, 0, C), C mod 2 =:= 1.
crossings([_], _, _, C, C) :- !.
crossings([[XJ, YJ], [XI, YI]|Ps], X, Y, C0, C) :-
    (   ( (YI > Y, YJ =< Y) ; (YI =< Y, YJ > Y) ), X < (XJ - XI) * (Y - YI) / (YJ - YI) + XI
    ->  C1 is C0 + 1 ; C1 = C0 ),
    crossings([[XI, YI]|Ps], X, Y, C1, C).

% the item under a point: topmost, in a shown and unlocked layer; top: the outermost item
hit(Sc, X, Y, Top, Deep) :-
    Sc = sc(Ls, _, _), reverse(Ls, TopFirst),
    (   member(layer(_, _, true, false, Items), TopFirst), reverse(Items, IT), member(N, IT), hit_in(N, X, Y, D)
    ->  node_id(N, Top), Deep = D
    ;   Top = null, Deep = null ).
hit_in(g(_, Kids), X, Y, D) :- !, reverse(Kids, KT), member(K, KT), hit_in(K, X, Y, D), !.
hit_in(N, X, Y, Id) :- covers(N, X, Y), node_id(N, Id).

% ------------------------------------------------------------------ menus
% a menu is a list of dicts: type "item" (label, goal, key?, enabled?), "menu" (label, items), "sep"

usable(E) :- is_dict(E), \+ get_dict(type, E, "sep"), \+ get_dict(enabled, E, false).
entry_at(Menu, Path, E) :- entry_at_(Path, Menu, null, E).
entry_at_([], _, E, E).
entry_at_([I|Is], Items, _, E) :- is_list(Items), nth0(I, Items, E1), !,
    ( get_dict(type, E1, "menu") -> get_dict(items, E1, Next) ; Next = null ), entry_at_(Is, Next, E1, E).
entry_at_(_, _, _, null).
list_at_path(Menu, [], Menu) :- !.
list_at_path(Menu, Path, Items) :- entry_at(Menu, Path, E), get_dict(items, E, Items).

% the next usable entry after I in a direction, wrapping; -1 if none
step(Items, I, Dir, J) :- length(Items, N), ( between(1, N, K), J is (I + Dir * K) mod N, nth0(J, Items, E), usable(E) -> true ; J = -1 ).
first(Items, J) :- step(Items, -1, 1, J).

menu_key(Menu, [], K, _{path: P}) :- !,
    ( memberchk(K, ["down", "enter", "right"]) -> first(Menu, F), ( F < 0 -> P = [] ; P = [F] ) ; P = [] ).
menu_key(Menu, Path, K, Out) :-
    append(Parent, [I], Path),
    list_at_path(Menu, Parent, Items),
    ( nth0(I, Items, E) -> true ; E = null ),
    (   ( K == "down" ; K == "up" )
    ->  ( K == "down" -> D = 1 ; D = -1 ), step(Items, I, D, J), ( J < 0 -> P = Path ; append(Parent, [J], P) ), Out = _{path: P}
    ;   ( K == "right" ; K == "enter" )
    ->  (   is_dict(E), get_dict(type, E, "menu")
        ->  get_dict(items, E, Sub), first(Sub, F), ( F < 0 -> P = Path ; append(Path, [F], P) ), Out = _{path: P}
        ;   K == "enter", usable(E) -> get_dict(goal, E, G), Out = _{path: [], run: G, closed: true}
        ;   Out = _{path: Path} )
    ;   K == "left" -> ( Parent \== [] -> Out = _{path: Parent} ; Out = _{path: Path} )
    ;   K == "escape" -> ( Parent \== [] -> Out = _{path: Parent} ; Out = _{path: [], closed: true} )
    ;   Out = _{path: Path} ).

menu_choose(Menu, Path, Out) :-
    entry_at(Menu, Path, E),
    (   \+ usable(E) -> append(Up, [_], Path), Out = _{path: Up}
    ;   get_dict(type, E, "menu") -> get_dict(items, E, Sub), first(Sub, F), ( F < 0 -> P = Path ; append(Path, [F], P) ), Out = _{path: P}
    ;   get_dict(goal, E, G), Out = _{path: [], run: G, closed: true} ).

% a shortcut: the first usable item with the key (either case), depth first
shortcut(Items, K, G) :- ( shortcut_(Items, K, G0) -> G = G0 ; G = null ).
shortcut_(Items, K, G) :-
    member(E, Items),
    (   get_dict(type, E, "item"), usable(E), get_dict(key, E, Key), string_lower(Key, L), string_lower(K, L) -> get_dict(goal, E, G)
    ;   get_dict(type, E, "menu"), \+ get_dict(enabled, E, false), get_dict(items, E, Sub), shortcut_(Sub, K, G) ), !.

% ------------------------------------------------------------------ painting

% the pixels of a line, both ends included (Bresenham)
line_points(X0, Y0, X1, Y1, Ps) :-
    DX is abs(X1 - X0), DY is -abs(Y1 - Y0),
    ( X0 < X1 -> SX = 1 ; SX = -1 ), ( Y0 < Y1 -> SY = 1 ; SY = -1 ),
    E is DX + DY, bres(X0, Y0, X1, Y1, DX, DY, SX, SY, E, Ps).
bres(X, Y, X, Y, _, _, _, _, _, [[X, Y]]) :- !.
bres(X, Y, X1, Y1, DX, DY, SX, SY, E, [[X, Y]|Ps]) :-
    E2 is 2 * E,
    ( E2 >= DY -> Ea is E + DY, Xn is X + SX ; Ea = E, Xn = X ),
    ( E2 =< DX -> Eb is Ea + DX, Yn is Y + SY ; Eb = Ea, Yn = Y ),
    bres(Xn, Yn, X1, Y1, DX, DY, SX, SY, Eb, Ps).

% flood fill on a grid (rows): the cells joined to (X, Y) up, down, left and right with its colour
cell(Rows, X, Y, C) :- nth0(Y, Rows, Row), nth0(X, Row, C).
fill_grid(Rows, X, Y, C, Out) :-
    length(Rows, H), Rows = [R0|_], length(R0, W),
    (   X >= 0, Y >= 0, X < W, Y < H, cell(Rows, X, Y, From), From =\= C
    ->  component(Rows, W, H, From, [X-Y], [X-Y], Comp),
        findall(Row, ( between(1, H, J1), J is J1 - 1,
                       findall(V, ( between(1, W, I1), I is I1 - 1, ( memberchk(I-J, Comp) -> V = C ; cell(Rows, I, J, V) ) ), Row) ), Out)
    ;   Out = Rows ).
component(_, _, _, _, [], Seen, Seen).
component(Rows, W, H, From, [X-Y|Q], Seen, Comp) :-
    findall(NX-NY, ( member(DX-DY, [1-0, -1-0, 0-1, 0-(-1)]), NX is X + DX, NY is Y + DY,
                     NX >= 0, NY >= 0, NX < W, NY < H, \+ memberchk(NX-NY, Seen), cell(Rows, NX, NY, From) ), New0),
    sort(New0, New), append(Seen, New, Seen1), append(Q, New, Q1),
    component(Rows, W, H, From, Q1, Seen1, Comp).

% a brush dot of colour 1 on a W by H grid of 0s
dot_grid(W, H, CX, CY, Size, Tip, Rows) :-
    R is Size / 2,
    findall(Row, ( between(1, H, J1), Y is J1 - 1,
                   findall(V, ( between(1, W, I1), X is I1 - 1, ( in_tip(Tip, R, X - CX, Y - CY) -> V = 1 ; V = 0 ) ), Row) ), Rows).
in_tip("round", R, DX0, DY0) :- DX is DX0, DY is DY0, DX * DX + DY * DY =< R * R + 0.25.
in_tip("square", R, DX0, DY0) :- IR is round(max(0, R)), abs(DX0) =< IR, abs(DY0) =< IR.

% ------------------------------------------------------------------ pointers

system_pointer(P) :- memberchk(P, ["arrow", "crosshair", "move", "grab", "grabbing", "text", "hand", "none", "cell", "forbidden"]).
cursor(P, _{w: 0, h: 0, hot: [0, 0]}) :- string(P), !,
    ( system_pointer(P) -> true ; err("~w isn't a pointer (try arrow, crosshair, move, grab, grabbing, text, hand, none, cell, forbidden)", [P]) ).
cursor(D, Out) :- is_dict(D), get_dict(f, D, F), get_dict(a, D, A), cursor(F, A, Out), !.
cursor(_, _) :- err("a pointer is a name (crosshair, move, ...), circle(R, Colour), cross(Size, Colour), glyph(Text) or svg(Text, X, Y)", []).
cursor("circle", [R0, C], _{w: S, h: S, hot: [M, M]}) :- in_range(R0, 1, 60, "circle radius", R), colour_ok(C), S is 2 * R + 4, M is S / 2.
cursor("cross", [Z0, C], _{w: S, h: S, hot: [M, M]}) :- in_range(Z0, 4, 64, "cross size", Z), colour_ok(C), S is Z + 2, M is S / 2.
cursor("glyph", [T], _{w: 32, h: 32, hot: [16, 16]}) :- glyph_ok(T).
cursor("glyph", [T, X0, Y0], _{w: 32, h: 32, hot: [X, Y]}) :- glyph_ok(T), in_range(X0, 0, 32, "hot spot x", X), in_range(Y0, 0, 32, "hot spot y", Y).
cursor("svg", [T, X0, Y0], _{w: W, h: H, hot: [X, Y]}) :-
    (   string(T), sub_string(T, 0, 4, _, "<svg"), sub_string(T, 4, 1, _, Nx), ( Nx == ">" ; char_type_space(Nx) ),
        attr_number(T, "width=\"", W), attr_number(T, "height=\"", H), W > 0, H > 0, W =< 128, H =< 128
    ->  true ; err("svg: an <svg> with width and height up to 128", []) ),
    ( unsafe_svg(T) -> err("svg: no scripts, events or links", []) ; true ),
    in_range(X0, 0, W, "hot spot x", X), in_range(Y0, 0, H, "hot spot y", Y).
in_range(V, Lo, Hi, What, R) :- ( number(V), V >= Lo, V =< Hi -> R is round(V) ; err("~w: ~w to ~w", [What, Lo, Hi]) ).
colour_ok(C) :- ( string(C), colour_text(C) -> true ; err("~w: a colour such as red or #ff8800", [C]) ).
colour_text(C) :- string_chars(C, ['#'|Hs]), length(Hs, N), ( N =:= 3 ; N =:= 6 ), maplist(hex_char, Hs), !.
colour_text(C) :- string_chars(C, Cs), length(Cs, N), N >= 3, N =< 12, maplist(small, Cs).
hex_char(C) :- char_type(C, xdigit(_)).
glyph_ok(T) :- ( string(T), string_length(T, N), N >= 1, N =< 3 -> true ; err("glyph: one to three characters", []) ).
char_type_space(S) :- string_chars(S, [C]), char_type(C, space).
% the number after the first Attr that a run of digits and a closing quote follow
attr_number(T, Attr, N) :- sub_string(T, B, _, _, Attr), string_length(Attr, AL), S is B + AL, digits_from(T, S, Ds), Ds \== [], E is S + 0, length(Ds, DL), Q is E + DL, sub_string(T, Q, 1, _, "\""), !, number_codes(N, Ds).
digits_from(T, S, [D|Ds]) :- sub_string(T, S, 1, _, C), string_codes(C, [D]), D >= 0'0, D =< 0'9, !, S1 is S + 1, digits_from(T, S1, Ds).
digits_from(_, _, []).
unsafe_svg(T) :- string_lower(T, L), ( sub_string(L, _, _, _, "<script") ; sub_string(L, _, _, _, "href=") ; on_attribute(L) ), !.
on_attribute(L) :- sub_string(L, B, 2, _, "on"), B > 0, B1 is B - 1, sub_string(L, B1, 1, _, Sp), char_type_space(Sp),
    S is B + 2, word_run(L, S, E), E > S, sub_string(L, E, 1, _, "=").
word_run(L, S, E) :- ( sub_string(L, S, 1, _, C), string_chars(C, [Ch]), word_char(Ch) -> S1 is S + 1, word_run(L, S1, E) ; E = S ).

% ------------------------------------------------------------------ the cases

spec(script, [Ops], Out) :- script(Ops, Out).
spec(hit, [Ops, X, Y], _{top: T, deep: D}) :- build(Ops, Sc), hit(Sc, X, Y, T, D).
spec(bounds, [Ops, Id], Out) :- build(Ops, Sc), catch(sc_bounds(Sc, Id, Out), ps(M), Out = _{error: M}).
spec(menuKey, [M, P, K], Out) :- menu_key(M, P, K, Out).
spec(menuChoose, [M, P], Out) :- menu_choose(M, P, Out).
spec(shortcut, [M, K], G) :- shortcut(M, K, G).
spec(line, [X0, Y0, X1, Y1], Ps) :- line_points(X0, Y0, X1, Y1, Ps).
spec(fill, [Rows, X, Y, C], Out) :- fill_grid(Rows, X, Y, C, Out).
spec(dot, [W, H, X, Y, S, T], Out) :- dot_grid(W, H, X, Y, S, T, Out).
spec(cursor, [P], Out) :- catch(cursor(P, Out), ps(M), Out = _{error: M}).
