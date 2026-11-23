% Paint: a painting program, all in PrologScript.
%
% Paint with the mouse, a pen or a finger. Right-click (or hold a finger down) for the pop-up
% menu: Brush, Colour (Warm, Cool, Plain) and Size. Drag a colour from the palette onto the
% picture to fill that part. Keys: b brush, q square, s spray, f fill, e eraser; Ctrl-Z undo.

title("Paint").
canvas(900, 560, white).

% ---- the menu bar
menu_bar([
    menu("File", [item("New picture", new_picture, [key(n)]),
                  item("Save picture", save_picture("Painting"), [key(p)])]),
    menu("Edit", [item("Undo", undo, [key(z)]),
                  item("Fill where I last tapped", fill_here)]),
    menu("Brush", Brushes),
    menu("Colour", Colours),
    menu("Size", Sizes)
]) :-
    brushes(Brushes), colours(Colours), sizes(Sizes).

% ---- the same choices, in a pop-up menu with menus inside menus
popup_menu(context, [
    menu("Brush", Brushes),
    menu("Colour", Colours),
    menu("Size", Sizes),
    separator,
    item("Fill here", fill_here),
    item("Undo", undo),
    item("Clear the picture", new_picture)
]) :-
    brushes(Brushes), colours(Colours), sizes(Sizes).

brushes([item("Round brush", use_tool(round), [checked(tool_is(round)), key(b)]),
         item("Square brush", use_tool(square), [checked(tool_is(square)), key(q)]),
         item("Spray can", use_tool(spray), [checked(tool_is(spray)), key(s)]),
         item("Fill bucket", use_tool(fill), [checked(tool_is(fill)), key(f)]),
         item("Eraser", use_tool(eraser), [checked(tool_is(eraser)), key(e)])]).

% Colour › Warm › Red: each family is a submenu, made from the colour/2 facts
colours([menu("Warm", Warm), menu("Cool", Cool), menu("Plain", Plain)]) :-
    swatches(warm, Warm), swatches(cool, Cool), swatches(plain, Plain).
swatches(Family, Items) :-
    findall(item(Label, use_colour(C), [checked(brush_is(colour, C))]),
            colour(Family, C, Label), Items).

colour(warm, red, "Red").      colour(warm, orange, "Orange").  colour(warm, yellow, "Yellow").
colour(warm, pink, "Pink").    colour(warm, brown, "Brown").    colour(warm, gold, "Gold").
colour(cool, blue, "Blue").    colour(cool, sky, "Sky").        colour(cool, teal, "Teal").
colour(cool, green, "Green").  colour(cool, purple, "Purple").   colour(cool, navy, "Navy").
colour(plain, black, "Black"). colour(plain, grey, "Grey").     colour(plain, white, "White").

sizes(Items) :-
    findall(item(Label, use_size(S), [checked(brush_is(size, S))]),
            ( member(S, [2, 6, 12, 24, 48]), format(string(Label), "~w pixels", [S]) ),
            Items).

% ---- the palette: drag a colour onto the picture to fill that part
palette([tile("Red", swatch(red), "🟥"), tile("Orange", swatch(orange), "🟧"),
         tile("Yellow", swatch(yellow), "🟨"), tile("Green", swatch(green), "🟩"),
         tile("Blue", swatch(blue), "🟦"), tile("Purple", swatch(purple), "🟪")]).

% ---- pointers: the brush's own size and colour, a bucket, a spray can
pointer_shape(bucket, glyph("🪣", 6, 26)).
pointer_shape(spray, glyph("💨")).

% ---- starting
on(start) :-
    nb_setval(tool, round), nb_setval(last, none),
    brush(colour, navy), brush(size, 12),
    show_brush,
    say("Paint with the mouse or a finger. Right-click (or hold a finger down) for the menu.").

% ---- painting: Prolog paints as the pointer moves
on(down(X, Y)) :- tool_is(fill), !, paint(fill(X, Y)).
on(down(X, Y)) :- tool_is(spray), !, paint(spray(X, Y)).
on(down(X, Y)) :- with_tool(paint(dot(X, Y))), nb_setval(last, X-Y).

on(drag(X, Y)) :- tool_is(spray), !, paint(spray(X, Y)).
on(drag(X, Y)) :-
    nb_getval(last, X0-Y0),
    with_tool(paint(line(X0, Y0, X, Y))),
    nb_setval(last, X-Y).

on(up(_, _)) :- nb_setval(last, none).

% a colour dropped from the palette fills where it lands
on(drop(swatch(C), X, Y)) :-
    brush(colour, Was), brush(colour, C),
    paint(fill(X, Y)),
    brush(colour, Was),
    say(["Filled with ", C, "."]).

% the eraser paints with the background colour
with_tool(Goal) :-
    tool_is(eraser), !,
    brush(colour, Was), brush(colour, white), call(Goal), brush(colour, Was).
with_tool(Goal) :- call(Goal).

% ---- the choices
use_tool(T) :-
    nb_setval(tool, T),
    ( T == square -> brush(tip, square) ; brush(tip, round) ),
    show_brush,
    tool_name(T, Name), say(Name).
tool_is(T) :- nb_getval(tool, T).
tool_name(round, "Round brush"). tool_name(square, "Square brush"). tool_name(spray, "Spray can").
tool_name(fill, "Fill bucket: tap a part of the picture."). tool_name(eraser, "Eraser").

use_colour(C) :- brush(colour, C), show_brush, say(["Colour: ", C]).
use_size(S) :- brush(size, S), show_brush.

fill_here :- pointer_at(X, Y), paint(fill(X, Y)).
new_picture :- paint(clear), say("A new picture.").

% the pointer shows what a tap will do
show_brush :- tool_is(T), brush(size, S), brush(colour, C), pointer_for(T, S, C).
pointer_for(fill, _, _) :- !, pointer(bucket).
pointer_for(spray, _, _) :- !, pointer(spray).
pointer_for(eraser, S, _) :- !, R is max(2, S // 2), pointer(circle(R, grey)).
pointer_for(_, S, C) :- R is max(2, S // 2), pointer(circle(R, C)).
