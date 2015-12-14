effect E : int

let _ =
  (try () with effect e k -> delegate e k);
  print_string "abc"
