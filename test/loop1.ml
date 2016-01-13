let x =
  let i = ref 0 in
  while true do
    incr i;
    print_int !i;
    print_endline ""
  done
