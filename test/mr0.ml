let rec f () =
  print_int 3;
  g ()
and g () =
  print_int 4;
  f ()

let x =
  f ()
