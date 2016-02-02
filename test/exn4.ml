let _ =
  print_int (
    try
      int_of_string (Sys.argv.(1))
    with _ -> 18
  )
