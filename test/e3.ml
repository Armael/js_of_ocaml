effect E : int

let _ =
  try
    print_string "abc";
    print_int (perform E);
    print_string "def";
  with effect E k ->
    continue k 18;
    print_string "handler end"
