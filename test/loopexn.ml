let rec f () =
  try
    print_endline ".";
    raise Exit
  with
  | Exit -> f ()

let _ =
  f()
