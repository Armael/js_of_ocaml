let f a =
  print_int a;
  fun b ->
    print_int b;
    fun c ->
      print_int c

let f' a b c =
  print_int a; print_int b; print_int c

let _ =
  f 1 2;
  let g = f' 1 2 in
  g 3; g 3
  (* let g () = f 1 2 in *)
  (* g () 3; g () 3 *)
