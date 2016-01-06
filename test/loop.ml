effect E : string

let x =
  try
    for i = 0 to 10 do
      print_int i;
      print_string (perform E);
    done
  with effect E k -> continue k "."
