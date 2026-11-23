tute("Vector shapes", "Rectangles, circles, lines, polygons and text").

lesson(1, "Shapes",
"`shape(Id, Shape, Style)` draws a shape that stays a shape: it can be changed, moved or deleted later, unlike paint. Shapes are `rect(X, Y, W, H)`, `square(X, Y, S)`, `circle(X, Y, R)`, `ellipse(X, Y, RX, RY)`, `line(X1, Y1, X2, Y2)`, `polygon([X-Y, ...])`, `path([X-Y, ...])` and `text(X, Y, Size, Text)`. A style is a list of `fill(C)`, `stroke(C)` and `width(W)`.

`new_id(Prefix, Id)` gives a fresh name: dot1, dot2, ...").
check(1, "tap to add three more circles.", (shapes(S), length(S, N), N >= 6)).
:- begin(1).
canvas(600, 360, white).
on(start) :-
    shape(sky, rect(0, 0, 600, 200), [fill(sky), stroke(none)]),
    shape(sun, circle(500, 70, 40), [fill(gold), stroke(orange), width(4)]),
    shape(hello, text(30, 330, 32, "Tap to add circles"), [fill(navy)]).
on(down(X, Y)) :- new_id(dot, Id), shape(Id, circle(X, Y, 18), [fill(red), stroke(black), width(2)]).
:- end(1).

lesson(2, "Changing shapes",
"`shape_at(X, Y, Id)` finds the topmost shape under a point. `restyle(Id, Style)` changes its colours or line; `reshape(Id, Shape)` changes its geometry; `delete(Id)` removes it. `style_of(Id, Style)` and `shape_of(Id, Shape)` read them back.").
check(2, "tap the box to colour it gold.", style_of(box, [fill("#ffb300")|_])).
:- begin(2).
canvas(600, 360, white).
on(start) :-
    shape(box, rect(60, 60, 160, 110), [fill(white), stroke(navy), width(3)]),
    shape(ball, circle(400, 160, 60), [fill(white), stroke(navy), width(3)]),
    say("Tap a shape to colour it. Press d, then tap, to delete.").
on(key(d)) :- nb_setval(mode, delete).
on(down(X, Y)) :- shape_at(X, Y, Id), catch(nb_getval(mode, delete), _, fail), !, delete(Id), nb_setval(mode, colour).
on(down(X, Y)) :- shape_at(X, Y, Id), restyle(Id, [fill(gold)]), say(["Coloured ", Id]).
:- end(2).

lesson(3, "Moving shapes",
"`move(Id, DX, DY)` moves a shape. To drag one, remember which shape was pressed and where, then move it by each drag's difference.").
check(3, "drag the box to the right half.", (bounds(box, [X|_]), X > 300)).
:- begin(3).
canvas(600, 360, white).
on(start) :- shape(box, rect(40, 120, 120, 90), [fill(sky), stroke(navy), width(3)]), say("Drag the box.").
on(down(X, Y)) :- shape_at(X, Y, Id), nb_setval(held, Id-X-Y).
on(drag(X, Y)) :- nb_getval(held, Id-X0-Y0), Id \== none,
    DX is X - X0, DY is Y - Y0, move(Id, DX, DY), nb_setval(held, Id-X-Y).
on(up(_, _)) :- nb_setval(held, none-0-0).
:- end(3).
