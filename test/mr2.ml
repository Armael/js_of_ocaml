let rec f () =
  print_int 3;
  g (); g ()
and g () =
  print_int 4;
  f (); f()

let x =
  f ()
