let _ =
  print_int (
    match String.length "abc" with
    | n -> 3 / 0
    | exception _ -> 42
  )
