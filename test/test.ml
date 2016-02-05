open OUnit2
open Batteries

let runjs = "node"

let is_str s stream =
  assert_equal s (Stream.to_string stream)

let starts_with s stream =
  let stream' = Stream.take (String.length s) stream in
  assert_equal s (Stream.to_string stream')

let ends_with s stream =
  let stream_s = Stream.to_string stream in
  assert_bool "ends_with" (String.ends_with stream_s s)

let assert_js
    ?exit_code
    ?sinput
    ?foutput
    ?use_stderr
    ?backtrace
    ?chdir
    ?env
    ~ctxt
    js_filename =
  assert_command ?exit_code ?sinput ?foutput ?use_stderr ?backtrace
    ?chdir ?env ~ctxt runjs [js_filename ^ ".js"]

let loops
  ?(foutput = ignore)
  js_filename =
  let (read, _) = Unix.pipe () in
  let (read_out, write) = Unix.pipe () in

  let pid = Unix.create_process runjs
      [|runjs; js_filename ^ ".js"|]
      read write Unix.stderr in

  Unix.sleep 1;
  begin match Unix.waitpid [Unix.WNOHANG] pid with
    | (0, _) ->
      Unix.kill pid 15;
      let cin = Legacy.Unix.in_channel_of_descr read_out in
      foutput (Stream.of_channel cin);
      true
    | _ ->
      false
  end

let test_pure =
  "pure" >::: [
    "n0: unit" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "") "n0");
    "n00: fun & funapp" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "") "n00");
    "f: fundecl" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "") "f");
    "n1: funapp, print_int" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "3\n") "n1");
    "p: seq of print_string" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "abc18def\n") "p");
    "p2: seq of print_string / funapp" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str ">3<>4<\n") "p2");

    "printf" >:: (fun ctxt ->
      assert_js ~ctxt
        ~foutput:(is_str "abc\n3\n3 4\na b cde\n")
        "print");
    "pf: also printf" >:: (fun ctxt ->
      assert_js ~ctxt
        ~foutput:(is_str "slt abc 3 4.000000 a\n") "pf");
    "apply" >:: (fun ctxt ->
      assert_js ~ctxt
        ~foutput:(is_str "a\nb\nc\n") "apply");
    "apply2" >:: (fun ctxt ->
      assert_js ~ctxt
        ~foutput:(is_str "a\nb\nc\na\nd\ne\n") "apply2");
  ]

let test_effects =
  "effects" >::: [
    "e01" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "3\n") "e01");
    "e1" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "abc18def\n") "e1");
    "e2" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "abc18def\n") "e2");
    "e3" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "abc18defhandler end\n") "e3");
    "e4" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "abc\n") "e4");
    "e5" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "hf1\nhf1\nhv\nhf2\nhf2\n") "e5");
    "e6" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "42\n") "e6");
    "MVar_test" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(ends_with "After put: 100\n") "MVar_test");
  ]

let test_ifs =
  "ifs" >::: [
    "if0" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "4\n") "if0");
    "if1" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "45\n") "if1");
  ]

let test_loops =
  "loops" >::: [
    "loop1" >:: (fun ctxt ->
      assert_bool "doesn't loop"
        (loops ~foutput:(starts_with "1\n2\n3\n4\n") "loop1"));
    "loop0" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "012345678910\n") "loop0");
    "loop" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "0.1.2.3.4.5.6.7.8.9.10.\n") "loop");
    "while" >:: (fun ctxt ->
      assert_bool "doesn't loop"
        (loops ~foutput:(starts_with ".\n.\n.\n.\n.") "while"));
    "while1" >:: (fun ctxt ->
      assert_bool "doesn't loop"
        (loops ~foutput:(starts_with ".\n-\n.\n-\n.\n-") "while1"));
    "looploop" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "12345678910111213141516171819202345678910111213141516171819202134567891011121314151617181920212245678910111213141516171819202122235678910111213141516171819202122232467891011121314151617181920212223242578910111213141516171819202122232425268910111213141516171819202122232425262791011121314151617181920212223242526272810111213141516171819202122232425262728291112131415161718192021222324252627282930\n") "looploop");
  ]

let test_recursion =
  "recursion" >::: [
    "rec" >:: (fun ctxt ->
      assert_bool "doesn't loop"
        (loops ~foutput:(starts_with ".\n.\n.\n.\n.") "rec"));
    "mr" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(ends_with "3\n4\n3\n4\n3\n4\n3\n4\n3\n4\n3\n4\n3\n") "mr");
    "mr0" >:: (fun ctxt ->
      assert_bool "doesn't loop"
        (loops ~foutput:(starts_with "3\n4\n3\n4\n3\n4\n3\n4\n3\n4\n3\n4\n3\n") "mr0"));
  ]

let test_exn =
  "exceptions" >::: [
    "mwe: match w/ exception; former jsoo bug" >:: (fun ctxt ->
      assert_js ~ctxt ~use_stderr:true ~exit_code:(Unix.WEXITED 1)
        ~foutput:(ends_with "Division_by_zero,-6\n") "mwe");
    "exn0" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "3\n") "exn0");
    "exn1" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "toto4\n") "exn1");
    "exn2" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "4\n") "exn2");
    "raise" >:: (fun ctxt ->
      assert_js ~ctxt ~use_stderr:true ~exit_code:(Unix.WEXITED 1)
        ~foutput:(ends_with "Failure,-3,abc\n") "raise");
    "exn3" >:: (fun ctxt ->
      assert_bool "loops" (not (loops "exn3"));
      assert_js ~ctxt ~foutput:(is_str "2\n") "exn3");
    "ex9" >:: (fun ctxt ->
      assert_js ~ctxt ~foutput:(is_str "1\n") "ex9");
    "exn4" >:: (fun ctxt ->
      assert_js ~ctxt ~use_stderr:true ~foutput:(is_str "18\n") "exn4");
    "loopexn" >:: (fun ctxt ->
      assert_bool "doesn't loop"
        (loops ~foutput:(starts_with ".\n.\n.\n.\n.") "loopexn"));
  ]

let tests =
  "tests" >::: [
    test_pure;
    test_effects;
    test_ifs;
    test_loops;
    test_recursion;
    test_exn;
  ]

let () =
  run_test_tt_main tests
