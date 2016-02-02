let _ =
  print_int (
    try
      (try raise Exit with
         Exit -> 2)
    with _ -> 1
  )
