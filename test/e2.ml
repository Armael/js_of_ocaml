effect E : int

let _ =
  try
    try
      print_string "abc";
      print_int (perform E);
      print_string "def"
    with effect e k -> delegate e k
  with effect E k -> continue k 18
