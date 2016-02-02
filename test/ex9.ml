effect E : int

let _ =
  print_int (
    try
      try perform E with
      | _ -> 0
      | effect E k -> raise Exit
    with
    | _ -> 1
  )
