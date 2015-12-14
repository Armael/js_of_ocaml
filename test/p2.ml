let f x =
  print_string ">"; print_int x; print_string "<"; x + 1

let _ =
  f (f 3)
