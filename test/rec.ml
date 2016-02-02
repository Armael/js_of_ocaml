let rec f () =
  print_endline ".";
  f ()

let _ = f ()
