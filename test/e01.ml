effect E : unit

let x =
  print_int (try 3 with effect E k -> 4)
