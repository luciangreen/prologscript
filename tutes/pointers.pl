tute("Pointers", "System pointers, brush rings, glyphs and SVG").

lesson(1, "The system's pointers",
"`pointer(Name)` sets the pointer over the canvas: `arrow`, `crosshair`, `move`, `grab`, `grabbing`, `text`, `hand`, `cell`, `forbidden` or `none`. `pointer_now(P)` reads it back as it was given. (On a phone there is no pointer to see, but the program still works.)").
check(1, "press 4 for the hand.", pointer_now(hand)).
:- begin(1).
canvas(600, 360, white).
on(start) :- pointer(crosshair), say("Press 1 to 5 and move over the canvas.").
on(key('1')) :- pointer(crosshair).
on(key('2')) :- pointer(move).
on(key('3')) :- pointer(text).
on(key('4')) :- pointer(hand).
on(key('5')) :- pointer(forbidden).
:- end(1).

lesson(2, "A ring the brush's size",
"`pointer(circle(R, Colour))` is a ring of radius R, so it shows exactly what a dot will cover. Change the brush with the up and down keys and the ring follows.").
check(2, "press up until the ring's radius is 20 or more.", (pointer_now(circle(R, _)), R >= 20)).
:- begin(2).
canvas(600, 360, white).
on(start) :- brush(size, 10), brush(colour, red), ring, say("Up and down change the brush.").
on(key(up)) :- brush(size, S), S2 is min(100, S + 6), brush(size, S2), ring.
on(key(down)) :- brush(size, S), S2 is max(2, S - 6), brush(size, S2), ring.
ring :- brush(size, S), brush(colour, C), R is max(1, S // 2), pointer(circle(R, C)).
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(2).

lesson(3, "Glyphs and your own drawings",
"`glyph(Text)` makes a pointer from a character or emoji, and `glyph(Text, X, Y)` says where its hot spot is. `svg(Text, X, Y)` is your own SVG, up to 128 by 128. `pointer_shape(Name, Spec)` gives one a name to use with `pointer(Name)`.").
check(3, "press s for the star pointer.", pointer_now(star)).
:- begin(3).
canvas(600, 360, white).
pointer_shape(star, glyph("⭐")).
pointer_shape(pin, glyph("📍", 16, 30)).
pointer_shape(target, svg("<svg width=\"32\" height=\"32\"><circle cx=\"16\" cy=\"16\" r=\"12\" fill=\"none\" stroke=\"red\" stroke-width=\"3\"/><circle cx=\"16\" cy=\"16\" r=\"3\" fill=\"red\"/></svg>", 16, 16)).
on(start) :- pointer(pin), say("s: star, p: pin, t: target. Tap to stamp it.").
on(key(s)) :- pointer(star), nb_setval(stamp, "⭐").
on(key(p)) :- pointer(pin), nb_setval(stamp, "📍").
on(key(t)) :- pointer(target), nb_setval(stamp, "◎").
on(down(X, Y)) :- catch(nb_getval(stamp, S), _, S = "📍"), new_id(stamp, Id), shape(Id, text(X, Y, 28, S), []).
:- end(3).
