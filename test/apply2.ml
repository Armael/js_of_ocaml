let f x y z =
  print_endline x; print_endline y; print_endline z

let () =
  let g = f "a" in
  g "b" "c"; g "d" "e"
