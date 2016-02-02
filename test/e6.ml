effect E : int

let _ =
  print_int (
    try perform E with
    | _ -> 0
    | effect E k -> 42
  )
