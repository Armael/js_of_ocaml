let _ =
  print_int (
    try String.length "toto"      
    with Exit ->
      (try String.length "abc" with
        Not_found -> 4)
  )
