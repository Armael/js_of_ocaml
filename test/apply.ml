let f x =
  print_endline x;
  fun y ->
    print_endline y;
    fun z ->
      print_endline z

let () =
  f "a" "b" "c"
