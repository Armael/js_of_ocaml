effect E : unit

let x =
  try 3 with effect E k -> 4
