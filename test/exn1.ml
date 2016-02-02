let _ =
  print_int (
    try
      if (Some 0) != (Some 0) then
        raise Exit
      else
        3
    with Exit ->
      print_string "toto";
      4
  )
