% Draw: a drawing program (vector graphics), all in PrologScript.
%
% Pick a tool from Tools (or press v, r, o, l, p, t), then drag on the page. With the Select
% tool, tap a shape to select it, drag to move it, drag a corner to resize it, drag across empty
% space to select several, and shift-tap to add one. Right-click (or hold a finger down) for the
% pop-up menu: Arrange › Order, Group; Style › Fill › Warm, ...; Layer › Move to ›. Drag a shape
% from the palette onto the page. The Layers panel shows each layer and the groups in it.

title("Draw").
canvas(900, 560, white).
panel(layers).
palette([tile("Star", star, "⭐"), tile("Heart", heart, "❤️"),
         tile("House", house, "🏠"), tile("Note", note, "🗒️")]).

% ---- the menu bar
menu_bar([
    menu("File", [item("New drawing", new_drawing),
                  item("Save drawing (SVG)", save_drawing("Drawing"), [key(s)]),
                  item("Save picture (PNG)", save_picture("Drawing"))]),
    menu("Edit", [item("Undo", undo, [key(z)]),
                  item("Select all", select_all, [key(a)]),
                  item("Delete", delete_selected, [enabled(something_selected)])]),
    menu("Tools", Tools),
    menu("Arrange", Arrange),
    menu("Style", Style),
    menu("Layer", Layer)
]) :-
    tools(Tools), arrange(Arrange), style_menu(Style), layer_menu(Layer).

% ---- the pop-up menu: the same menus, inside one another
popup_menu(context, [
    menu("Arrange", Arrange),
    menu("Style", Style),
    menu("Layer", Layer),
    menu("Tools", Tools),
    separator,
    item("Delete", delete_selected, [enabled(something_selected)])
]) :-
    tools(Tools), arrange(Arrange), style_menu(Style), layer_menu(Layer).

tools(Items) :-
    findall(item(Label, use_tool(T), [checked(tool_is(T)), key(K)]), tool(T, Label, K, _), Items).
tool(select,  "Select",  v, arrow).
tool(rect,    "Rectangle", r, crosshair).
tool(ellipse, "Ellipse", o, crosshair).
tool(line,    "Line",    l, crosshair).
tool(pen,     "Pen",     p, glyph("✏️", 3, 28)).
tool(text,    "Text",    t, text).

arrange([
    menu("Order", [item("Bring to front", each_selected(front)),
                   item("Bring forward", each_selected(raise)),
                   item("Send backward", each_selected(lower)),
                   item("Send to back", each_selected(back))]),
    menu("Group", [item("Group", group_selected, [key(g), enabled(several_selected)]),
                   item("Ungroup", ungroup_selected, [key(u), enabled(a_group_selected)])]),
    menu("Nudge", [item("Left", nudge(-10, 0)), item("Right", nudge(10, 0)),
                   item("Up", nudge(0, -10)), item("Down", nudge(0, 10))])
]).

% Style › Fill › Warm › Red: colours in families, families in a menu, the menu in Style
style_menu([
    menu("Fill", [menu("Warm", Warm), menu("Cool", Cool), item("No fill", set_style(fill, none), [checked(style_is(fill, none))])]),
    menu("Line colour", [menu("Warm", WarmL), menu("Cool", CoolL), menu("Plain", PlainL)]),
    menu("Line width", Widths)
]) :-
    colour_items(fill, warm, Warm), colour_items(fill, cool, Cool),
    colour_items(line, warm, WarmL), colour_items(line, cool, CoolL), colour_items(line, plain, PlainL),
    findall(item(L, set_style(width, W), [checked(style_is(width, W))]),
            ( member(W, [1, 2, 4, 8, 16]), format(string(L), "~w", [W]) ), Widths).
colour_items(Part, Family, Items) :-
    findall(item(Label, set_style(Part, C), [checked(style_is(Part, C))]), colour(Family, C, Label), Items).

colour(warm, red, "Red").     colour(warm, orange, "Orange").  colour(warm, yellow, "Yellow").
colour(warm, pink, "Pink").   colour(warm, gold, "Gold").
colour(cool, sky, "Sky").     colour(cool, blue, "Blue").      colour(cool, teal, "Teal").
colour(cool, green, "Green"). colour(cool, purple, "Purple").  colour(cool, navy, "Navy").
colour(plain, black, "Black"). colour(plain, grey, "Grey").    colour(plain, white, "White").

% Layer › Use layer › and Layer › Move selection to ›: menus made from the layers there now
layer_menu([
    item("New layer", add_layer, [key(n)]),
    menu("Use layer", from(layer_items(use_layer))),
    menu("Move selection to", from(layer_items(move_to_layer))),
    separator,
    item("Hide this layer", hide_active),
    item("Show every layer", show_all),
    item("Lock this layer", lock_active, [checked(active_locked)]),
    item("Raise this layer", active_layer_do(layer_up)),
    item("Lower this layer", active_layer_do(layer_down)),
    item("Delete this layer", active_layer_do(delete_layer))
]).
layer_items(Action, Items) :-
    layers(Bottom), reverse(Bottom, Top),
    findall(item(Name, Goal, [checked(active_layer(L))]),
            ( member(L, Top), layer_name(L, Name), Goal =.. [Action, L] ), Items).

% ---- starting: two layers, and a little scene on the back one
on(start) :-
    rename_layer(layer1, "Back"),
    shape(sun, circle(780, 90, 50), [fill(gold), stroke(orange), width(4)]),
    shape(hill, ellipse(250, 600, 420, 160), [fill(green), stroke(none)]),
    new_layer(front, "Front"),
    nb_setval(tool, select), nb_setval(drawing, none),
    nb_setval(fill, sky), nb_setval(line, navy), nb_setval(width, 3),
    pointer(arrow),
    say("Pick a tool and drag on the page. Right-click (or hold a finger down) for the menu.").

% ---- the Select tool: the built-in editor does the selecting, moving and resizing
on(down(X, Y)) :- tool_is(select), !, ( held(shift) -> edit(add_down(X, Y)) ; edit(down(X, Y)) ).
on(drag(X, Y)) :- tool_is(select), !, edit(drag(X, Y)).
on(up(X, Y))   :- tool_is(select), !, edit(up(X, Y)).

% ---- the other tools: a new shape, which grows as you drag
on(down(X, Y)) :-
    tool_is(T), new_id(T, Id), style_now(Style),
    start_shape(T, Id, X, Y, Style),
    nb_setval(drawing, Id-X-Y), select([Id]).
on(drag(X, Y)) :- nb_getval(drawing, Id-X0-Y0), grow(Id, X0, Y0, X, Y).
on(up(_, _)) :- nb_setval(drawing, none).

start_shape(rect, Id, X, Y, S)    :- shape(Id, rect(X, Y, 1, 1), S).
start_shape(ellipse, Id, X, Y, S) :- shape(Id, ellipse(X, Y, 1, 1), S).
start_shape(line, Id, X, Y, S)    :- shape(Id, line(X, Y, X, Y), S).
start_shape(pen, Id, X, Y, S)     :- shape(Id, path([X-Y, X-Y]), S).
start_shape(text, Id, X, Y, _)    :- nb_getval(line, C), shape(Id, text(X, Y, 28, "Hello"), [fill(C)]).

grow(Id, X0, Y0, X, Y) :-
    shape_of(Id, rect(_, _, _, _)), !,
    L is min(X0, X), T is min(Y0, Y), W is abs(X - X0), H is abs(Y - Y0),
    reshape(Id, rect(L, T, W, H)).
grow(Id, X0, Y0, X, Y) :-
    shape_of(Id, ellipse(_, _, _, _)), !,
    CX is (X0 + X) / 2, CY is (Y0 + Y) / 2, RX is abs(X - X0) / 2, RY is abs(Y - Y0) / 2,
    reshape(Id, ellipse(CX, CY, RX, RY)).
grow(Id, X0, Y0, X, Y) :- shape_of(Id, line(_, _, _, _)), !, reshape(Id, line(X0, Y0, X, Y)).
grow(Id, _, _, X, Y) :- shape_of(Id, path(Ps)), !, append(Ps, [X-Y], Ps2), reshape(Id, path(Ps2)).
grow(Id, _, _, X, Y) :- shape_of(Id, text(_, _, Size, T)), reshape(Id, text(X, Y, Size, T)).

% ---- the palette: shapes dropped onto the page
on(drop(star, X, Y)) :-
    new_id(star, Id), style_now(S),
    findall(PX-PY, ( between(0, 9, K), A is K * pi / 5 - pi / 2,
                     ( K mod 2 =:= 0 -> R = 50 ; R = 22 ),
                     PX is round(X + R * cos(A)), PY is round(Y + R * sin(A)) ), Ps),
    shape(Id, polygon(Ps), S), select([Id]).
on(drop(heart, X, Y)) :-
    new_id(heart, Id),
    findall(PX-PY, ( between(0, 35, K), T is K * pi / 18,
                     PX is round(X + 3 * 16 * sin(T) ** 3),
                     PY is round(Y - 3 * (13 * cos(T) - 5 * cos(2*T) - 2 * cos(3*T) - cos(4*T))) ), Ps),
    shape(Id, polygon(Ps), [fill(red), stroke(pink), width(3)]), select([Id]).
% a house is a group of shapes: walls, roof, door; it moves and resizes as one
on(drop(house, X, Y)) :-
    new_id(house, H), atom_concat(H, '_walls', W), atom_concat(H, '_roof', R), atom_concat(H, '_door', D),
    L is X - 60, T is Y - 20, RL is X - 75, RR is X + 75, Top is Y - 80, DL is X - 15, DT is Y + 20,
    shape(W, rect(L, T, 120, 90), [fill(cream), stroke(brown), width(3)]),
    shape(R, polygon([RL-T, X-Top, RR-T]), [fill(red), stroke(brown), width(3)]),
    shape(D, rect(DL, DT, 30, 50), [fill(brown), stroke(brown)]),
    group([W, R, D], H), select([H]).
on(drop(note, X, Y)) :-
    new_id(note, N), atom_concat(N, '_paper', P), atom_concat(N, '_words', Wd),
    L is X - 70, T is Y - 40, TX is X - 55, TY is Y + 6,
    shape(P, rect(L, T, 140, 80), [fill(yellow), stroke(gold), width(2)]),
    shape(Wd, text(TX, TY, 22, "A note"), [fill(navy)]),
    group([P, Wd], N), select([N]).

% ---- keys
on(key(delete)) :- delete_selected.
on(key(backspace)) :- delete_selected.
on(key(escape)) :- select([]).
on(key(left)) :- nudge(-5, 0).
on(key(right)) :- nudge(5, 0).
on(key(up)) :- nudge(0, -5).
on(key(down)) :- nudge(0, 5).

% ---- the choices
use_tool(T) :- nb_setval(tool, T), tool(T, Label, _, Pointer), pointer(Pointer), say(Label).
tool_is(T) :- nb_getval(tool, T).

style_now([fill(F), stroke(L), width(W)]) :- nb_getval(fill, F), nb_getval(line, L), nb_getval(width, W).
set_style(Part, V) :-
    nb_setval(Part, V),
    style_term(Part, V, St),
    selection(Ids), forall(member(I, Ids), restyle(I, [St])).
style_term(fill, V, fill(V)).
style_term(line, V, stroke(V)).
style_term(width, V, width(V)).
style_is(Part, V) :- nb_getval(Part, V).

something_selected :- selection([_|_]).
several_selected :- selection([_, _|_]).
a_group_selected :- selection([G]), shape_of(G, group(_)).

each_selected(How) :- selection(Ids), forall(member(I, Ids), call(How, I)).
nudge(DX, DY) :- selection(Ids), forall(member(I, Ids), move(I, DX, DY)).
delete_selected :- selection(Ids), forall(member(I, Ids), delete(I)).
select_all :- active_layer(L), items_in(L, Ids), select(Ids).

group_selected :- selection(Ids), new_id(group, G), group(Ids, G), select([G]), say(["Grouped as ", G]).
ungroup_selected :- selection([G]), shape_of(G, group(Items)), ungroup(G), select(Items).

add_layer :- layers(Ls), length(Ls, N), N1 is N + 1, atom_concat(layer, N1, Id0),
    ( layer_name(Id0, _) -> new_id(layer, Id) ; Id = Id0 ),
    format(string(Name), "Layer ~w", [N1]), new_layer(Id, Name), say(["New layer: ", Name]).
move_to_layer(L) :- selection(Ids), forall(member(I, Ids), to_layer(I, L)).
hide_active :- active_layer(L), show_layer(L, false).
show_all :- layers(Ls), forall(member(L, Ls), show_layer(L, true)).
lock_active :- active_layer(L), ( active_locked -> lock_layer(L, false) ; lock_layer(L, true) ).
active_locked :- active_layer(L), layer_locked(L).
active_layer_do(Command) :- active_layer(L), call(Command, L).

new_drawing :- shapes(All), forall(member(I, All), catch(delete(I), _, true)), say("A new drawing.").
