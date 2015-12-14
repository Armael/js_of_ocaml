effect E : unit

let _ =
  match
    perform E; perform E
  with
  | _ -> print_endline "hv"
  | effect E k ->
    print_endline "hf1";
    continue k ();
    print_endline "hf2"
