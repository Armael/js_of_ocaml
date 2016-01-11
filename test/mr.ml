let x = ref 0
let max = 100

let rec f () =
  print_int 3;
  incr x;
  if !x <= max then
    g ()
and g () =
  print_int 4;
  incr x;
  if !x <= max then
    f ()

let x =
  f ()
