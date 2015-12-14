effect E : unit

let x =
  try
    for i = 0 to 100 do
      perform E
    done
  with effect E k -> continue k ()
