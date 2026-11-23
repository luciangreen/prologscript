tute("Drag and drop", "A palette, drop events, and dragging into a bin").

lesson(1, "A palette",
"`palette(Tiles)` shows tiles beside the canvas; each is `tile(Label, Thing, Icon)`. Drag a tile onto the canvas (with the mouse or a finger) and the program hears `drop(Thing, X, Y)`.").
check(1, "drag two balls onto the canvas.", (shapes(S), length(S, N), N >= 2)).
:- begin(1).
canvas(600, 360, white).
palette([tile("Ball", ball, "⚽"), tile("Block", block, "🟫")]).
on(start) :- say("Drag a tile onto the canvas.").
on(drop(ball, X, Y)) :- new_id(ball, Id), shape(Id, circle(X, Y, 30), [fill(white), stroke(black), width(3)]).
on(drop(block, X, Y)) :- new_id(block, Id), L is X - 30, T is Y - 30, shape(Id, square(L, T, 60), [fill(brown)]).
:- end(1).

lesson(2, "What lands where",
"A Thing can be any term, such as `paint(red)`. The drop's point says where it landed, so `shape_at/3` finds what it landed on.").
check(2, "drag the red paint onto the box.", style_of(box, [fill("#e53935")|_])).
:- begin(2).
canvas(600, 360, white).
palette([tile("Red", paint(red), "🟥"), tile("Blue", paint(blue), "🟦"), tile("Green", paint(green), "🟩")]).
on(start) :-
    shape(box, rect(60, 90, 180, 140), [fill(white), stroke(black), width(3)]),
    shape(ball, circle(420, 160, 70), [fill(white), stroke(black), width(3)]),
    say("Drop paint on a shape.").
on(drop(paint(C), X, Y)) :- shape_at(X, Y, Id), restyle(Id, [fill(C)]), say(["Painted ", Id, " ", C]).
on(drop(paint(_), _, _)) :- say("That landed on nothing.").
:- end(2).

lesson(3, "Dragging into a bin",
"Shapes already on the canvas can be dragged and dropped too: remember the shape on `down`, move it on `drag`, and on `up` look at where it was let go. Here a shape let go over the bin is deleted.").
check(3, "drag the apple into the bin.", \+ shape_of(apple, _)).
:- begin(3).
canvas(600, 360, white).
on(start) :-
    shape(bin, rect(440, 200, 120, 130), [fill(grey), stroke(black), width(3)]),
    shape(label, text(462, 280, 24, "Bin"), [fill(white)]),
    group([bin, label], the_bin), lock_layer(layer1, false),
    shape(apple, circle(120, 120, 35), [fill(red)]),
    shape(pear, ellipse(250, 150, 28, 40), [fill(lime)]),
    say("Drag the fruit into the bin.").
on(down(X, Y)) :- shape_at(X, Y, Id), Id \== the_bin, nb_setval(held, Id-X-Y).
on(drag(X, Y)) :- nb_getval(held, Id-X0-Y0), Id \== none,
    DX is X - X0, DY is Y - Y0, move(Id, DX, DY), nb_setval(held, Id-X-Y).
on(up(X, Y)) :- nb_getval(held, Id-_-_), Id \== none, nb_setval(held, none-0-0),
    bounds(the_bin, [BX, BY, BW, BH]), X >= BX, X =< BX + BW, Y >= BY, Y =< BY + BH,
    delete(Id), say(["Binned the ", Id]).
on(up(_, _)) :- nb_setval(held, none-0-0).
:- end(3).
