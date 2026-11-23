tute("The editor", "Select, move, resize and select many with edit/1").

lesson(1, "The editor",
"Handing pointer events to `edit/1` gives you an editor without writing one: `edit(down(X, Y))`, `edit(drag(X, Y))` and `edit(up(X, Y))`. Tap a shape to select it and drag to move it.").
check(1, "drag the blue box to the right half.", (bounds(box, [X|_]), X > 300)).
:- begin(1).
canvas(600, 360, white).
on(start) :-
    shape(box, rect(40, 100, 140, 100), [fill(sky), stroke(navy), width(3)]),
    shape(ball, circle(420, 220, 50), [fill(pink), stroke(purple), width(3)]),
    say("Tap to select, drag to move.").
on(down(X, Y)) :- edit(down(X, Y)).
on(drag(X, Y)) :- edit(drag(X, Y)).
on(up(X, Y)) :- edit(up(X, Y)).
:- end(1).

lesson(2, "Selecting many",
"Drag across empty space to select everything inside the band. `selection(Ids)` says what's selected, and `select(Ids)` sets it. Held keys are asked with `held(shift)`: shift-tap adds to the selection with `edit(add_down(X, Y))`.").
check(2, "select two or more shapes (drag a band around them, or shift-tap).", (selection(S), length(S, N), N >= 2)).
:- begin(2).
canvas(600, 360, white).
on(start) :-
    shape(a, square(60, 60, 70), [fill(gold)]),
    shape(b, circle(250, 100, 40), [fill(teal)]),
    shape(c, rect(380, 200, 150, 80), [fill(pink)]).
on(down(X, Y)) :- ( held(shift) -> edit(add_down(X, Y)) ; edit(down(X, Y)) ).
on(drag(X, Y)) :- edit(drag(X, Y)).
on(up(X, Y)) :- edit(up(X, Y)), selection(S), say(["Selected: ", S]).
:- end(2).

lesson(3, "Resizing",
"When one shape (or group) is selected, it has four corner handles: drag one to resize. Groups resize as one, everything inside scaled. `resize(Id, [X, Y, W, H])` does it from Prolog.").
check(3, "select the box and drag a corner out until it is wider than 200.", (bounds(box, [_, _, W, _]), W > 200)).
:- begin(3).
canvas(600, 360, white).
on(start) :- shape(box, rect(80, 80, 120, 80), [fill(sky), stroke(navy), width(3)]), select([box]).
on(down(X, Y)) :- edit(down(X, Y)).
on(drag(X, Y)) :- edit(drag(X, Y)).
on(up(X, Y)) :- edit(up(X, Y)).
on(key(r)) :- resize(box, [80, 80, 120, 80]).
:- end(3).
