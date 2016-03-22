(*******************************************************************)
(* Amthing Example3. bounce ball                                   *)
(*******************************************************************)
open Ccell
open Event
open Amthing.Util.Pervasives

module W = Amthing.Core.Window ( Amthing.XWindow )
module K = Amthing.KeyCode
module E = Amthing.WinEvent
module S = Amthing.Sprite
module C = Amthing.Component
module T = Amthing.Tween
module B = Amthing.Behavior
let wh = W.make (Amthing.XWindow.default_parameter ())

let pi = acos ~-.1.

let add_bounce_behavior c =
  let up =
    T.behavior [`Y 50.] ~time:0.5 ~transit:`Linear
  in
  let down =
    T.behavior [`Y 200.] ~time:0.5 ~transit:`Linear
  in
  C.update c (B.over @@ B.loop @@ B.append down up)

let ball =
  let area gc me =
    Cairo.arc gc ~xc:0. ~yc:0. ~radius:10. ~angle1:~-.pi ~angle2:pi;
  in
  let draw_ball gc me =
    Amthing.Color.set gc me#color 1.;
    area gc me;
    Cairo.fill gc
  in
  new S.sprite
  +> S.set (`X 100.)
  +> S.set (`Y 200.)
  +> S.set (`Color Amthing.Color.blue)
  +> S.set (`Appear [draw_ball])
  +> S.set (`Area area)
  +> C.make

let _ =
  wh#resize {| x = 0; y = 0; w = 200; h = 200 |};
  add_bounce_behavior ball;
  wh#add_visible ball;
  wh#set_title "amthing bounce ball example";
  wh#show ~fps:20;
  let main_loop () =
    match sync @@ Bcast.receive wh#event with
      `KEY_PRESS input when E.key_code input = Some K._q ->
	    wh#close;
	    exit 0
    | #E.t -> ()
  in
  forever main_loop ()
