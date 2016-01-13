effect E : unit

let x =
  try
    while true do
      print_endline ".";
      perform E
    done
  with effect E k -> continue k (print_endline "-")
