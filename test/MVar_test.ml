open Printf

open MVar.M
open MVar.Sched

let mv = create_empty ()

let fork f = perform @@ Fork f

let put x =
  (printf "Before put: %s\n" x;
  put x mv;
  printf "After put: %s\n" x)

let get () =
  let () = printf "Before get\n" in
  let v = take mv in
  let () = printf "After get: %s\n" v in
  v

(* let main () = *)
(*   put "0"; *)
(*   for i = 1 to 100 do *)
(*     fork (fun () -> put (string_of_int i)); *)
(*   done; *)
(*   for i = 0 to 100 do *)
(*     fork (fun () -> ignore (get ())); *)
(*   done *)

let main () =
  put "0";
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> put "i");
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()));
  fork (fun () -> ignore (get ()))

let () = run main
