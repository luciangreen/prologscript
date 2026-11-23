% Theorems about PrologScript's core (proofs/spec.pl), each proved by exhaustion over a small
% domain: every script of operations, every grid, every menu, every line of a size.
%
% Run:  swipl -g main -t halt proofs/theorems.pl      (exit status 1 if a theorem fails)

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module('spec.pl').
:- discontiguous theorem/1.

r(Id, X, Y, ["add", Id, "rect", [X, Y, 10, 10], _{fill: "#e53935"}]).

% ------------------------------------------------------------------ the scene

% the operations tried (some of them fail, which must leave the scene as it was)
op(O) :- member(O, [
    ["add", "d", "ellipse", [5, 5, 4, 4], _{}],
    ["group", ["a", "b"], "g"], ["group", ["a"], "h"], ["group", ["g", "c"], "k"],
    ["ungroup", "g"], ["remove", "a"], ["remove", "g"], ["move", "g", 1, 1],
    ["restack", "b", "front"], ["restack", "c", "back"],
    ["addLayer", "top", "Top"], ["toLayer", "c", "top"], ["toLayer", "g", "top"],
    ["setLayer", "layer1", "locked", true], ["select", ["a", "c"]]]).
start(Sc) :- empty(E), r("a", 0, 0, A), r("b", 5, 5, B), r("c", 20, 0, C),
    foldl([O, S0, S]>>apply_op(O, S0, S), [A, B, C], E, Sc).
step(Sc0, Sc) :- op(O), catch(apply_op(O, Sc0, Sc), ps(_), Sc = Sc0).

% every operation, in every order of up to three, keeps the scene well formed: each shape or
% group in exactly one place, the selection only of what is there, the layer in use there
theorem(operations_keep_the_scene_well_formed) :-
    start(S0),
    forall(( step(S0, S1), step(S1, S2), step(S2, S3) ), ( well_formed(S1), well_formed(S2), well_formed(S3) )).

% nothing changes what a locked layer holds: no operation, nor any two in a row
theorem(a_locked_layer_does_not_change) :-
    start(S), apply_op(["setLayer", "layer1", "locked", true], S, S0), held(S0, H0),
    forall(( step(S0, S1), step(S1, S2) ), ( locked_still(S2) -> held(S2, H0) ; true )).
locked_still(sc(Ls, _, _)) :- memberchk(layer("layer1", _, _, true, _), Ls).
held(Sc, H) :- outline(Sc, O), memberchk(["layer1", H0], O), Sc = sc(Ls, _, _), memberchk(layer("layer1", _, _, _, Items), Ls), H = H0-Items.

% grouping keeps every item, keeps the members together in their stacking order and puts the
% rest in their order; ungrouping straight after gives the list back when the members were
% already side by side
theorem(group_then_ungroup) :-
    Ids = ["a", "b", "c", "d"],
    forall(( subseq(Ids, Members), Members \== [] ),
        ( empty(E), findall(O, ( member(I, Ids), r(I, 0, 0, O) ), Adds),
          foldl([O, S0, S]>>apply_op(O, S0, S), Adds, E, Sc0),
          apply_op(["group", Members, "g"], Sc0, Sc1), outline(Sc1, [[_, L1]]),
          select(["g", Members], L1, Rest), subtract(Ids, Members, Rest),
          apply_op(["ungroup", "g"], Sc1, Sc2), outline(Sc2, [[_, L2]]),
          msort(L2, Sorted), msort(Ids, Sorted),
          ( append(_, Tail, Ids), append(Members, _, Tail) -> L2 == Ids ; true ) )).
subseq([], []).
subseq([X|Xs], [X|Ys]) :- subseq(Xs, Ys).
subseq([_|Xs], Ys) :- subseq(Xs, Ys).

% restacking moves one item and nothing else: to the front, the back, or one step
theorem(restacking_moves_one_item) :-
    forall(( between(1, 4, N), numlist(1, N, Ns), maplist([K, Id]>>format(string(Id), "s~w", [K]), Ns, Ids),
             member(Id, Ids), member(How, ["raise", "lower", "front", "back"]) ),
        ( empty(E), findall(O, ( member(I, Ids), r(I, 0, 0, O) ), Adds), foldl([O, S0, S]>>apply_op(O, S0, S), Adds, E, Sc0),
          apply_op(["restack", Id, How], Sc0, Sc), outline(Sc, [[_, L]]),
          msort(L, M), msort(Ids, M),
          exclude(==(Id), L, Others), exclude(==(Id), Ids, Others),
          nth0(I0, Ids, Id), nth0(I1, L, Id), Last is N - 1,
          ( How == "front" -> I1 =:= Last ; How == "back" -> I1 =:= 0
          ; How == "raise" -> I1 =:= min(Last, I0 + 1) ; I1 =:= max(0, I0 - 1) ) )).

% the item a tap finds is the topmost one under it, in a layer that is shown and unlocked;
% when it finds none, nothing shown and unlocked is there
theorem(a_tap_finds_the_topmost_item) :-
    forall(( scene_variant(Sc), between(0, 20, X2), between(0, 12, Y2), X is X2 * 2, Y is Y2 * 2 ),
        ( hit(Sc, X, Y, Top, _),
          drawn_top_first(Sc, Items),
          (   Top == null -> \+ ( member(N, Items), covering(N, X, Y) )
          ;   append(Above, [N|_], Items), item_id(N, Top), !, covering(N, X, Y), \+ ( member(M, Above), covering(M, X, Y) ) ) )).
scene_variant(Sc) :-
    member(Hide, [none, "layer1", "top"]), member(Lock, [none, "layer1", "top"]),
    empty(E),
    Ops = [["add", "a", "rect", [0, 0, 20, 20], _{fill: "#e53935"}], ["add", "b", "ellipse", [20, 12, 10, 6], _{}],
           ["add", "c", "line", [0, 24, 40, 0], _{width: 4}], ["group", ["a", "b"], "g"],
           ["addLayer", "top", "Top"], ["add", "d", "poly", [[10, 4], [30, 4], [20, 20]], _{fill: "#81d4fa"}],
           ["add", "e", "rect", [26, 10, 10, 10], _{}]],
    foldl([O, S0, S]>>apply_op(O, S0, S), Ops, E, Sc0),
    ( Hide == none -> Sc1 = Sc0 ; apply_op(["setLayer", Hide, "shown", false], Sc0, Sc1) ),
    ( Lock == none -> Sc = Sc1 ; apply_op(["setLayer", Lock, "locked", true], Sc1, Sc) ).
drawn_top_first(sc(Ls, _, _), Items) :-
    reverse(Ls, TL), findall(N, ( member(layer(_, _, true, false, Is), TL), reverse(Is, RI), member(N, RI) ), Items).
item_id(s(Id, _, _, _, _), Id).
item_id(g(Id, _), Id).
covering(N, X, Y) :- ps_spec:hit_in(N, X, Y, _), !.

% ------------------------------------------------------------------ menus

entry(_{type: "item", label: "I", goal: "go"}).
entry(_{type: "item", label: "D", goal: "no", enabled: false}).
entry(_{type: "sep"}).
entry(_{type: "menu", label: "M", items: [_{type: "item", label: "J", goal: "deep"}]}).
entry(_{type: "menu", label: "N", items: [_{type: "sep"}, _{type: "item", label: "K", goal: "k", enabled: false}]}).
menu(M) :- between(1, 3, N), length(M, N), maplist(entry, M).
path(M, [I]) :- length(M, N), Top is N - 1, between(0, Top, I).
path(M, [I, J]) :- nth0(I, M, E), get_dict(items, E, Sub), length(Sub, N), Top is N - 1, between(0, Top, J).

% moving through a menu with the keys only ever stops on an entry that can be chosen
theorem(menu_keys_stop_on_usable_entries) :-
    forall(( menu(M), path(M, P), member(K, ["up", "down", "right", "enter"]) ),
        ( menu_key(M, P, K, Out), get_dict(path, Out, P1),
          ( P1 == P ; P1 == [] ; ps_spec:entry_at(M, P1, E), usable(E) ) )).

% choosing an item runs exactly its goal and closes the menu; nothing else runs anything
theorem(only_items_run_goals) :-
    forall(( menu(M), path(M, P) ),
        ( menu_choose(M, P, Out), ps_spec:entry_at(M, P, E),
          ( get_dict(run, Out, G) -> usable(E), get_dict(type, E, "item"), get_dict(goal, E, G), get_dict(closed, Out, true)
          ; \+ ( usable(E), get_dict(type, E, "item") ) ) )).

% ------------------------------------------------------------------ painting

% a painted line starts and ends where it was asked to, with no gaps and no doubled pixels
theorem(lines_are_unbroken) :-
    forall(( member(X0, [-3, -2, -1, 0, 1, 2, 3]), member(Y0, [-3, -1, 0, 2, 3]), member(X1, [-3, -2, -1, 0, 1, 2, 3]), member(Y1, [-3, -1, 0, 2, 3]) ),
        ( line_points(X0, Y0, X1, Y1, Ps),
          Ps = [[X0, Y0]|_], last(Ps, [X1, Y1]),
          length(Ps, N), N =:= max(abs(X1 - X0), abs(Y1 - Y0)) + 1,
          forall(nextto([A, B], [C, D], Ps), ( abs(C - A) =< 1, abs(D - B) =< 1, [A, B] \== [C, D] )) )).

% flood fill changes only cells of the seed's colour, leaves none of them beside the filled
% region, and filling again changes nothing
theorem(fill_fills_exactly_the_region) :-
    forall(( grid3(G), between(0, 2, X), between(0, 2, Y), member(C, [0, 1, 2]) ),
        ( fill_grid(G, X, Y, C, F),
          nth0(Y, G, Row), nth0(X, Row, From),
          forall(( between(0, 2, I), between(0, 2, J), nth0(J, G, GR), nth0(I, GR, V0), nth0(J, F, FR), nth0(I, FR, V1), V0 \== V1 ),
                 ( V0 =:= From, V1 =:= C )),
          ( From =:= C -> F == G
          ; nth0(Y, F, FR0), nth0(X, FR0, C),
            \+ ( between(0, 2, I), between(0, 2, J), nth0(J, F, FR), nth0(I, FR, C), nth0(J, G, GR), nth0(I, GR, From),
                 member(DI-DJ, [1-0, -1-0, 0-1, 0-(-1)]), I2 is I + DI, J2 is J + DJ, between(0, 2, I2), between(0, 2, J2),
                 nth0(J2, F, FR2), nth0(I2, FR2, From) ) ),
          fill_grid(F, X, Y, C, F2), F2 == F )).
grid3([[A, B, C], [D, E, F], [G, H, I]]) :- maplist([V]>>member(V, [0, 1]), [A, B, C, D, E, F, G, H, I]).

% a brush dot is the same turned over either way, and a bigger brush covers what a smaller did
theorem(dots_are_symmetric_and_grow) :-
    forall(( member(T, ["round", "square"]), between(1, 9, S) ),
        ( dot_grid(11, 11, 5, 5, S, T, G),
          reverse(G, G), maplist(reverse, G, G2), G2 == G, transpose3(G, G),
          ( S < 9 -> S1 is S + 1, dot_grid(11, 11, 5, 5, S1, T, H), covered_by(G, H) ; true ) )).
transpose3(G, T) :- findall(Row, ( between(0, 10, I), findall(V, ( between(0, 10, J), nth0(J, G, R), nth0(I, R, V) ), Row) ), T).
covered_by(G, H) :- forall(( nth0(J, G, R), nth0(I, R, 1) ), ( nth0(J, H, RH), nth0(I, RH, 1) )).

% ------------------------------------------------------------------ pointers

% every pointer accepted fits the browser's 128 by 128, with its hot spot inside it
theorem(pointers_fit) :-
    forall(( ( between(1, 60, R), P = _{f: "circle", a: [R, "red"]}
             ; between(4, 64, Z), P = _{f: "cross", a: [Z, "#123"]}
             ; between(0, 32, X), member(Y, [0, 16, 32]), P = _{f: "glyph", a: ["x", X, Y]} ) ),
        ( cursor(P, C), get_dict(w, C, W), get_dict(h, C, H), get_dict(hot, C, [HX, HY]),
          W =< 128, H =< 128, HX >= 0, HY >= 0, HX =< W, HY =< H )).

main :-
    findall(T, clause(theorem(T), _), Ts),
    foldl([T, F0, F]>>( catch(theorem(T), E, (print_message(error, E), fail))
                         -> format("proved  ~w~n", [T]), F = F0
                         ;  format("FAILED  ~w~n", [T]), F is F0 + 1 ), Ts, 0, Failed),
    length(Ts, N),
    ( Failed =:= 0 -> format("~w theorems proved.~n", [N]) ; format("~w of ~w theorems failed.~n", [Failed, N]), halt(1) ).
