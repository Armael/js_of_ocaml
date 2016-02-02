let rec f () =
  print_endline "3";
  g ()
and g () =
  print_endline "4";
  f ()

let x =
  f ()
