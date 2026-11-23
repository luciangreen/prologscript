# PrologScript

PrologScript puts Prolog where a web page would use JavaScript. A program is ordinary Prolog: facts declare what is on screen, `on/1` clauses answer what you do, and commands such as `paint(line(...))`, `shape(Id, circle(...))` and `popup(context)` become things you see. These include:

- hierarchical menus and pop-up menus;
- painting;
- vector graphics in groups and layers, with an editor;
- drag and drop;
- custom pointers.

It is a plug-in for [Visual Starlog](https://github.com/luciangreen/visualstarlog) in [LucianOS](https://github.com/luciangreen/lucianos), where a slide can run a program. It is also an app of its own, with:

- **Paint** and **Draw**, two finished demos;
- a **tute** for each element;
- **My program** for your own.

There is also a **pack**, which works on its own without LucianOS ([below](#the-pack-without-lucianos)).

The code is always visible beside the running program. The clause that answered the last event is marked, and a trace lists each event, the commands it gave (with what they answered) and any error. Programs run in the page on the [pl2detlog](https://github.com/luciangreen/pl2detlog) Prolog interpreter (`vendor/pl2detlog.js`), so nothing needs installing and it works on an iPhone. Use a finger for drawing; hold a finger down for the pop-up menu.

## A program

```prolog
title("Doodle").
canvas(600, 360, white).

menu_bar([menu("Colour", [menu("Warm", [item("Red", brush(colour, red)), item("Orange", brush(colour, orange))]),
                          menu("Cool", [item("Blue", brush(colour, blue))])])]).
popup_menu(context, [item("Clear", paint(clear)), item("Undo", undo)]).

on(start) :- brush(size, 8), pointer(circle(4, navy)), say("Draw with the mouse or a finger.").
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
```

## What a program declares

| Fact | What it does |
| --- | --- |
| `title(Text)` | The program's name |
| `canvas(W, H, Background)` | The canvas, in its own units (it is scaled to fit the screen) |
| `menu_bar(Menus)` | The menu bar. It can be a rule; menus are read each time they open |
| `popup_menu(Name, Items)` | A pop-up menu. `context` opens on a right-click, or when a finger is held down, unless `on(right(X, Y))` answers |
| `pointer_shape(Name, Spec)` | A named pointer, for `pointer(Name)` |
| `palette(Tiles)` | Tiles beside the canvas, `tile(Label, Thing, Icon)`, to drag onto it |
| `panel(layers)` | The Layers panel: each layer, with its shapes and groups, which you can show, hide, lock and choose |

**Menu items** are written as follows:
- `item(Label, Goal)` or `item(Label, Goal, Options)`. The options are `key(K)` (a shortcut), `checked(Goal)` (a tick when Goal is true) and `enabled(Goal)` (greyed out when Goal isn't true).
- `menu(Label, Items)` nests to any depth.
- `menu(Label, from(Pred))` builds its items when it opens, with `call(Pred, Items)`.
- `separator` draws a line.

On a phone, submenus open one at a time, with a way back.

## Events: `on(Event)`

| Event | When |
| --- | --- |
| `start` | The program begins |
| `down(X, Y)`, `drag(X, Y)`, `up(X, Y)` | Press, move while pressed, let go (mouse, pen or finger) |
| `right(X, Y)` | A right-click, or a finger held down |
| `key(K)` | A key. Letters are themselves; also `up`, `down`, `left`, `right`, `enter`, `escape`, `delete`, `backspace`, `space` |
| `drop(Thing, X, Y)` | A palette tile dropped on the canvas |
| `hover(X, Y)` | Moving without pressing. It is sent only to programs with an `on(hover(..))` clause |

If no clause matches, nothing happens. A program remembers things between events with `nb_setval/2` and `nb_getval/2`.

## Commands

| | |
| --- | --- |
| Painting | `paint(dot(X,Y))`, `paint(line(X1,Y1,X2,Y2))`, `paint(fill(X,Y))`, `paint(spray(X,Y))`, `paint(clear)`; `brush(colour\|size\|tip, V)` (with V unbound, it reads); `brush_is(Key, V)` tests; `colour_at(X, Y, C)`, `painted(N)` |
| Shapes | `shape(Id, Shape)`, `shape(Id, Shape, Style)` with shapes `rect(X,Y,W,H)`, `square(X,Y,S)`, `circle(X,Y,R)`, `ellipse(X,Y,RX,RY)`, `line(X1,Y1,X2,Y2)`, `polygon([X-Y,..])`, `path([X-Y,..])`, `text(X,Y,Size,Text)` and styles `[fill(C), stroke(C), width(W)]`; `restyle/2`, `reshape/2`, `move(Id, DX, DY)`, `resize(Id, [X,Y,W,H])`, `delete/1`; `raise/1`, `lower/1`, `front/1`, `back/1` |
| Groups | `group(Ids, G)`, `ungroup(G)`, to any depth; `shape_of(G, group(Items))` |
| Looking | `shape_at(X, Y, Id)` (the outermost group), `part_at(X, Y, Id)` (the shape itself), `bounds(Id, [X,Y,W,H])`, `shape_of/2`, `style_of/2`, `shapes(Ids)`, `new_id(Prefix, Id)` |
| Layers | `new_layer(Id, Name)`, `use_layer/1`, `active_layer/1`, `layers/1`, `rename_layer/2`, `layer_name/2`, `show_layer(Id, true\|false)`, `lock_layer/2`, `layer_shown/1`, `layer_locked/1`, `items_in(Layer, Ids)`, `layer_up/1`, `layer_down/1`, `to_layer(Id, Layer)`, `delete_layer/1` |
| The editor | `edit(down(X,Y))`, `edit(drag(X,Y))`, `edit(up(X,Y))`, `edit(add_down(X,Y))`: tap to select, drag to move, drag a corner handle to resize, drag across empty space to select several; `select(Ids)`, `selection(Ids)`, `held(shift)` |
| On screen | `popup(Name)`, `pointer(Spec)`, `pointer_now(P)`, `pointer_at(X, Y)`, `say(Text or [Parts])`, `undo`, `save_picture(Name)` (PNG), `save_drawing(Name)` (SVG) |

**Pointers** can be:
- a system pointer: `arrow`, `crosshair`, `move`, `grab`, `grabbing`, `text`, `hand`, `none`, `cell` or `forbidden`;
- `circle(R, Colour)`, a ring the size of the brush;
- `cross(Size, Colour)`;
- `glyph(Text)` or `glyph(Text, X, Y)`, such as an emoji;
- `svg(Text, X, Y)`, up to 128 by 128, with no scripts.

**Mistakes:**
- A command that can't be done raises a Prolog error, which you can catch. The trace shows it, for example "box1 is already there" or "rect: not a shape I can draw".
- Each press, key, drop and menu choice is one step for `undo`.
- A program's own predicate with the same name as a command is used instead of the command.
- A locked layer can't be changed in any way.

## The demos

- `demos/paint.pl` is a painting program. It has round and square brushes, a spray can, a fill bucket and an eraser. The menu bar and the pop-up both have Brush, Colour › Warm/Cool/Plain › colour and Size, all with ticks. You can drag a colour from the palette onto the picture to fill that part, and the pointer is the brush's own size and colour. It also has undo and saving a PNG.
- `demos/draw.pl` is a drawing program. Its tools are select, rectangle, ellipse, line, pen and text. Its menus include Arrange › Order/Group/Nudge, Style › Fill › Warm › colour, and Layer › Use layer and Move selection to, whose items are made from the layers there now. Shapes can be dragged from the palette: a star, a heart, and a house and a note, each of which is a group. It also has the Layers panel, the editor's handles, undo, and saving SVG and PNG.

## The tutes

There is one tute for each element: menus, pop-up menus, events, painting, vector shapes, groups, layers, the editor, drag and drop, pointers, and state and visible code. Each tute is a PrologScript file (`tutes/*.pl`):
- each step is a program between `:- begin(N).` and `:- end(N).`;
- `lesson(N, Title, Says)` holds the lesson;
- `check(N, Hint, Goal)` holds the check, a Prolog goal asked of the learner's running program.

Run a step, change it, and press Check; the tick also comes by itself once it is done. Progress is kept in the browser.

## In Visual Starlog

Add an item of the kind *PrologScript program* to a slide and choose a `.pl` file from the presentation's folder, or write `prologscript("bubbles.pl")`. The program runs in the slide preview and when presenting, with its code in a fold underneath. While you use the program, the arrow keys are its own. The plug-in is `plugin.js`:

```js
import { mountProgram } from '../prologscript/plugin.js';
const ps = await mountProgram(element, source, { code: true });   // ps.destroy() stops it
```

## The pack, without LucianOS

The pack is PrologScript on its own. It needs no LucianOS, no server, nothing to install and no internet connection. Download it from the [releases](https://github.com/luciangreen/prologscript/releases), or build it with `npm install && npm run pack` (it goes in `dist/`).

| File | What it is |
| --- | --- |
| `prologscript.html` | The whole app in one file: Paint and Draw with their code, the tutes, and My program. Double-click it, send it, put it on a USB stick or any web host. It works on iPhone and Android. |
| `prologscript.js` | A drop-in script that puts PrologScript programs in your own pages (below). |
| `example.html` | A page that uses `prologscript.js`. |
| `prologscript-pack.zip` | All three, the demos and tutes as `.pl` files, a README and the licence. |

With `prologscript.js`, a page needs no JavaScript of its own. Each `<script type="text/prolog">` becomes the running program, in its place:

```html
<script src="prologscript.js"></script>
<script type="text/prolog">
canvas(400, 300, white).
popup_menu(context, [menu("Colour", [item("Red", brush(colour, red)), item("Blue", brush(colour, blue))])]).
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
</script>
```

- **`data-src="paint.pl"`:** reads the program from a file instead. The page must then be served, not opened from a folder.
- **`data-code="false"`:** hides the code fold under the program.
- **From JavaScript:** `PrologScript.mountProgram(element, source, { code: true })` mounts a program, and `PrologScript.mountScripts()` mounts any scripts added since the page loaded.

Each push builds the pack in CI (the Pack workflow). On `main`, the workflow also publishes the pack as the release for `package.json`'s version. To start a new release, raise the version.

## Install

In LucianOS, open Apps › App Store and install PrologScript (it brings Visual Starlog with it). By hand, run this from your `lucianos` folder:

```sh
git clone https://github.com/luciangreen/prologscript apps/prologscript
```

It is static files, so any web server will do: open `index.html`. For lucianos-web, put it beside lucianos-web and list it in `sources.json`.

## Proofs and the 200 inputs and outputs

The pure core is `lib/scene.js`, `lib/menu.js`, `lib/paint.js`, `lib/pointer.js` and `lib/editor.js`. `proofs/spec.pl` states it in Prolog as a model of its own: a scene is `sc(Layers, Active, Selected)`, with layers holding trees of `s/5` shapes and `g/2` groups.

- `io/ios.jsonl` (and `io/ios.txt`) hold 200 inputs and outputs recorded from the JavaScript. They cover scripts of scene operations (including the errors they raise), hit tests, bounds, menu keys, choosing and shortcuts, lines, flood fill, brush dots and pointers. `proofs/ios.pl` checks that the spec gives every one.
- `proofs/theorems.pl` proves 11 theorems by exhaustion:
  - every operation, in every order of up to three, keeps the scene well formed;
  - nothing changes a locked layer;
  - grouping and ungrouping keep every item and their order;
  - restacking moves one item and nothing else;
  - a tap finds the topmost item in a shown, unlocked layer;
  - menu keys only stop on entries that can be chosen;
  - only items run goals;
  - painted lines have no gaps;
  - flood fill fills exactly the region;
  - brush dots are symmetric and grow;
  - every pointer accepted fits in 128 by 128.

```sh
npm test       # unit tests; the demos driven by events; every tute step loaded and solved
npm run ios    # rewrite the 200 inputs and outputs
npm run proofs # needs swipl
```

## Licence

BSD-3-Clause.
