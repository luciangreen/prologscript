tute("Painting", "Brushes, lines, fill, spray and undo").

lesson(1, "Brushes",
"`brush(colour, C)`, `brush(size, S)` and `brush(tip, round)` or `square` set the brush. With an unbound value they read it: `brush(size, S)`. `brush_is(Key, Value)` only tests.

`paint(dot(X, Y))` and `paint(line(X1, Y1, X2, Y2))` paint with it.").
check(1, "paint a big patch with the square tip (press q).", (painted(N), N > 6000, brush_is(tip, square))).
:- begin(1).
canvas(600, 360, white).
on(start) :- brush(colour, green), brush(size, 16), say("Paint. q: square tip, r: round tip.").
on(key(q)) :- brush(tip, square).
on(key(r)) :- brush(tip, round).
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(1).

lesson(2, "Fill and spray",
"`paint(fill(X, Y))` fills the part of the picture joined to that point which has its colour. `paint(spray(X, Y))` sprays dots around the point. `paint(clear)` starts again.

The tool is remembered with `nb_setval(tool, T)`, and the first `on(down(...))` clause whose test is true answers.").
check(2, "draw a closed shape, press f, and tap the background outside it.", (colour_at(2, 2, C), C \== "#ffffff")).
:- begin(2).
canvas(600, 360, white).
on(start) :- nb_setval(tool, brush), brush(colour, purple), brush(size, 6), say("b: brush, f: fill, s: spray, c: clear").
on(key(b)) :- nb_setval(tool, brush).
on(key(f)) :- nb_setval(tool, fill), brush(colour, yellow).
on(key(s)) :- nb_setval(tool, spray), brush(colour, red).
on(key(c)) :- paint(clear).
on(down(X, Y)) :- nb_getval(tool, fill), !, paint(fill(X, Y)).
on(down(X, Y)) :- nb_getval(tool, spray), !, paint(spray(X, Y)).
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(tool, spray), !, paint(spray(X, Y)).
on(drag(X, Y)) :- nb_getval(tool, brush), nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(2).

lesson(3, "Undo, and reading the picture",
"Each press, key, drop or menu choice is one step that `undo` takes back. `colour_at(X, Y, C)` reads a pixel's colour, so this program's i key picks up a colour from the picture.").
check(3, "paint a stroke, then press u to undo it.", catch(nb_getval(undone, yes), _, fail)).
:- begin(3).
canvas(600, 360, white).
on(start) :- brush(size, 14), brush(colour, teal), paint(fill(0, 0)), brush(colour, orange),
    say("Paint, then u to undo. i picks up the colour where you last tapped.").
on(key(u)) :- undo, nb_setval(undone, yes), say("Undone.").
on(key(i)) :- pointer_at(X, Y), colour_at(X, Y, C), brush(colour, C), say(["Picked up ", C]).
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(3).
