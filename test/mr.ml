let x = ref 0
let max = 10000

let rec f () =
  print_endline "3";
  incr x;
  if !x <= max then
    g ()
and g () =
  print_endline "4";
  incr x;
  if !x <= max then
    f ()

let x =
  f ()
