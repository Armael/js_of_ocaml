effect E : unit

let _ =
  print_int (
    try

      (try
         raise Exit
       with effect E k -> ());
      2

    with effect E k -> 0
    | Exit -> 1
  )
