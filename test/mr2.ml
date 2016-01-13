let u () =
  let rec f () =
    print_int 3;
    g (); g ()
  and g () =
    print_int 4;
    f (); f()
  in
  f ()

let x =
  u ()
