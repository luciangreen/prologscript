tute("Groups", "Shapes in groups, groups in groups: levels").

lesson(1, "A group",
"`group(Ids, G)` puts shapes side by side into a group named G. The group moves, resizes and restyles as one, and `shape_at/3` finds the group, not the shape inside it.").
check(1, "drag the house to the right half.", (bounds(house, [X|_]), X > 300)).
:- begin(1).
canvas(600, 360, white).
on(start) :-
    shape(walls, rect(60, 160, 140, 110), [fill(cream), stroke(brown), width(3)]),
    shape(roof, polygon([45-160, 130-90, 215-160]), [fill(red), stroke(brown), width(3)]),
    shape(door, rect(115, 210, 30, 60), [fill(brown), stroke(brown)]),
    group([walls, roof, door], house),
    say("Drag the house: it moves as one.").
on(down(X, Y)) :- shape_at(X, Y, Id), nb_setval(held, Id-X-Y).
on(drag(X, Y)) :- nb_getval(held, Id-X0-Y0), Id \== none,
    DX is X - X0, DY is Y - Y0, move(Id, DX, DY), nb_setval(held, Id-X-Y).
on(up(_, _)) :- nb_setval(held, none-0-0).
:- end(1).

lesson(2, "Groups in groups",
"A group can hold groups, to any depth: here a street holds two houses, and each house holds its walls and roof. `shape_at(X, Y, Id)` gives the outermost group; `part_at(X, Y, Id)` gives the shape itself.").
check(2, "tap a roof.", (catch(nb_getval(part, P), _, fail), sub_atom(P, _, _, _, roof))).
:- begin(2).
canvas(600, 360, white).
on(start) :- house(a, 60), house(b, 300), group([a, b], street), say("Tap any part of a house.").
house(H, X) :-
    atom_concat(H, '_walls', W), atom_concat(H, '_roof', R),
    RL is X - 15, RT is X + 70, RR is X + 155,
    shape(W, rect(X, 170, 140, 100), [fill(cream), stroke(brown), width(3)]),
    shape(R, polygon([RL-170, RT-100, RR-170]), [fill(red), stroke(brown), width(3)]),
    group([W, R], H).
on(down(X, Y)) :- shape_at(X, Y, Top), part_at(X, Y, Part), nb_setval(part, Part),
    say(["shape_at says ", Top, "; part_at says ", Part]).
:- end(2).

lesson(3, "Ungrouping",
"`ungroup(G)` puts a group's shapes back where it was, in order. `shape_of(G, group(Items))` lists what a group holds.").
check(3, "press u to ungroup the street.", \+ shape_of(street, _)).
:- begin(3).
canvas(600, 360, white).
on(start) :-
    shape(a, circle(150, 180, 60), [fill(sky)]), shape(b, circle(400, 180, 60), [fill(pink)]),
    group([a, b], street), say("Press u to ungroup.").
on(key(u)) :- shape_of(street, group(Items)), ungroup(street), say(["Back to ", Items]).
:- end(3).
