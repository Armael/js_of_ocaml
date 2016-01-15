(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2010 Jérôme Vouillon
 * Laboratoire PPS - CNRS Université Paris Diderot
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, with linking exception;
 * either version 2.1 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

let debug = Option.Debug.find "main"
let times = Option.Debug.find "times"

module Primitive = Jsoo_primitive
open Util

let tailcall p =
  if debug () then Format.eprintf "Tail-call optimization...@.";
  Tailcall.f p

let deadcode' p =
  if debug () then Format.eprintf "Dead-code...@.";
  Jsoo_deadcode.f p

let deadcode p =
  let r,_ = deadcode' p
  in r

(* let no_deadcode p = *)
(*   p, Array.make (Code.Var.count ()) 1 *)

let inline p =
  if Option.Optim.inline () && Option.Optim.deadcode ()
  then
    let (p,live_vars) = deadcode' p in
    if debug () then Format.eprintf "Inlining...@.";
    Inline.f p live_vars
  else p

let specialize_1 (p,info) =
  if debug () then Format.eprintf "Specialize...@.";
  Specialize.f info p

let specialize_js (p,info) =
  if debug () then Format.eprintf "Specialize js...@.";
  Specialize_js.f info p

let specialize' (p,info) =
  let p = specialize_1 (p,info)in
  let p = specialize_js (p,info) in
  p,info

let specialize p =
  fst (specialize' p)

let eval (p,info) =
  if Option.Optim.staticeval()
  then Eval.f info p
  else p

let flow p =
  if debug () then Format.eprintf "Data flow...@.";
  Flow.f p

let flow_simple p =
  if debug () then Format.eprintf "Data flow...@.";
  Flow.f ~skip_param:true p

let phi p =
  if debug () then Format.eprintf "Variable passing simplification...@.";
  Phisimpl.f p

let print p =
  if debug () then Code.print_program (fun _ _ -> "") p; p

let (>>) f g = fun x -> g (f x)

let rec loop max name round i (p : 'a) : 'a =
  let p' = round p in
  if i >= max || Code.eq p' p
  then p'
  else
    begin
      if times ()
      then Format.eprintf "Start Iteration (%s) %d...@." name i;
      loop max name round (i+1) p'
    end

let identity x = x

(* o1 *)

let o0 : 'a -> 'a = print

let o1 : 'a -> 'a=
  print >>
  tailcall >>
  flow_simple >> (* flow simple to keep information for furture tailcall opt *)
  specialize' >>
  eval >>
  inline >> (* inlining may reveal new tailcall opt *)
  deadcode >>
  tailcall >>
  phi >>
  flow >>
  specialize >>
  inline >>
  deadcode >>
  print >>
  flow >>
  specialize >>
  inline >>
  deadcode >>
  phi >>
  flow >>
  specialize >>
  identity

(* o2 *)

let o2 : 'a -> 'a =
  loop 10 "o1" o1 1 >>
  print

(* o3 *)

let round1 : 'a -> 'a =
  print >>
  tailcall >>
  inline >> (* inlining may reveal new tailcall opt *)
  deadcode >>
  (* deadcode required before flow simple -> provided by constant *)
  flow_simple >> (* flow simple to keep information for furture tailcall opt *)
  specialize' >>
  eval >>
  identity

let round2 =
  flow >>
  specialize' >>
  eval >>
  deadcode >>
  o1

let o3 =
  loop 10 "tailcall+inline" round1 1 >>
  loop 10 "flow" round2 1 >>
  print

let generate d ?toplevel (p,live_vars) =
  if times ()
  then Format.eprintf "Start Generation...@.";
  Generate.f p ?toplevel live_vars d


let header formatter ~standalone js =
  if standalone then begin
    let version = match Compiler_version.git_version with
      | "" -> Compiler_version.s
      | v  -> Printf.sprintf "%s+git-%s"Compiler_version.s v in

    Pretty_print.string formatter
      ("// Generated by js_of_ocaml " ^ version);

    Pretty_print.newline formatter;
  end;
  js

let debug_linker = Option.Debug.find "linker"

let global_object = Option.global_object

let extra_js_files = lazy (
  List.fold_left (fun acc file ->
      try
        let ss = List.fold_left (fun ss (prov,_,_,_) ->
            match prov with
            | Some (_,name,_,_) -> StringSet.add name ss
            | _ -> ss
          ) StringSet.empty (Linker.parse_file file) in
        (file,ss)::acc
      with _ -> acc
    ) [] Option.extra_js_files
)

let report_missing_primitives missing =
  let missing =  List.fold_left (fun missing (file,pro) ->
      let d = StringSet.inter missing pro in
      if not (StringSet.is_empty d)
      then begin
        Util.warn "Missing primitives provided by %s:@." file;
        StringSet.iter (fun nm -> Util.warn "  %s@." nm) d;
        StringSet.diff missing pro
      end
      else missing
    ) missing (Lazy.force extra_js_files) in
  Util.warn "Missing primitives:@.";
  StringSet.iter (fun nm -> Util.warn "  %s@." nm) missing

let gen_missing js missing =
    let open Javascript in
    let miss = StringSet.fold (fun prim acc ->
        let p = S {name=prim;var=None} in
        (p,
         Some (
           ECond(EBin(NotEqEq,
                      EDot(EVar (S {name=global_object;var=None}),prim),
                      EVar(S {name="undefined";var=None})),
                 EDot(EVar (S {name=global_object;var=None}),prim),
                 EFun(None,[],[
                     Statement(
                       Expression_statement (
                         ECall(EVar (S {name="caml_failwith";var=None}),
                               [EBin(Plus,EStr(prim,`Utf8),
                                     EStr(" not implemented",`Utf8))], N))),
                     N],N)
                ),
           N
         )) :: acc
      ) missing [] in
    if not (StringSet.is_empty missing)
    then begin
      Util.warn "There are some missing primitives@.";
      Util.warn "Dummy implementations (raising 'Failure' exception) ";
      Util.warn "will be used if they are not available at runtime.@.";
      Util.warn "You can prevent the generation of dummy implementations with ";
      Util.warn "the commandline option '--disable genprim'@.";
      report_missing_primitives missing;
    end;
    (Statement (Variable_statement miss), N) :: js


let link ~standalone ?linkall js =
  if standalone
  then
    begin
      let t = Util.Timer.make () in
      if times ()
      then Format.eprintf "Start Linking...@.";
      let traverse = new Js_traverse.free in
      let js = traverse#program js in
      let free = traverse#get_free_name in

      let prim = Primitive.get_external () in
      let prov = Linker.get_provided () in

      let all_external = StringSet.union prim prov in

      let used = StringSet.inter free all_external in

      let linkinfos = Linker.init () in
      let linkinfos,missing = Linker.resolve_deps ?linkall linkinfos used in

      (* gen_missing may use caml_failwith *)
      let linkinfos,missing =
        if not (StringSet.is_empty missing) && Option.Optim.genprim ()
        then
          let linkinfos,missing2 = Linker.resolve_deps linkinfos (StringSet.singleton "caml_failwith") in
          linkinfos, StringSet.union missing missing2
        else linkinfos, missing in

      let js = if Option.Optim.genprim ()
        then gen_missing js missing
        else js in
      if times () then Format.eprintf "  linking: %a@." Util.Timer.print t;
      Linker.link js linkinfos
    end
  else js


let check_js ~standalone js =
  if standalone
  then
    begin
      let t = Util.Timer.make () in
      if times ()
      then Format.eprintf "Start Checks...@.";

      let traverse = new Js_traverse.free in
      let js = traverse#program js in
      let free = traverse#get_free_name in

      let prim = Primitive.get_external () in
      let prov = Linker.get_provided () in

      let all_external = StringSet.union prim prov in

      let missing = StringSet.inter free all_external in

      let other =  StringSet.diff free missing in

      let res = VarPrinter.get_reserved() in
      let other = StringSet.diff other res in
      if not (StringSet.is_empty missing)
      then begin
        report_missing_primitives missing
      end;

      let probably_prov = StringSet.inter other Reserved.provided in
      let other = StringSet.diff other probably_prov in

      if not (StringSet.is_empty other) && debug_linker ()
      then
        begin
          Util.warn "Missing variables:@.";
          StringSet.iter (fun nm -> Util.warn "  %s@." nm) other
        end;

      if not (StringSet.is_empty probably_prov) && debug_linker ()
      then
        begin
          Util.warn "Variables provided by the browser:@.";
          StringSet.iter (fun nm -> Util.warn "  %s@." nm) probably_prov
        end;
      if times () then Format.eprintf "  checks: %a@." Util.Timer.print t;
      js
    end
  else js

let coloring js =
  let t = Util.Timer.make () in
  if times ()
  then Format.eprintf "Start Coloring...@.";
  let traverse = new Js_traverse.free in
  let js = traverse#program js in
  let free = traverse#get_free_name in
  VarPrinter.add_reserved (StringSet.elements free);
  let js = Js_assign.program js in
  if times () then Format.eprintf "  coloring: %a@." Util.Timer.print t;
  js

let output formatter ?source_map js =
  let t = Util.Timer.make () in
  if times ()
  then Format.eprintf "Start Writing file...@.";
  Js_output.program formatter ?source_map js;
  if times () then Format.eprintf "  write: %a@." Util.Timer.print t

let pack ~wrap_with_fun ?(toplevel=false) js =
  let module J = Javascript in
  let t = Util.Timer.make () in
  if times ()
  then Format.eprintf "Start Optimizing js...@.";
  (* pre pack optim *)
  let js =
    if Option.Optim.share_constant ()
    then
      let t1 = Util.Timer.make () in
      let js = (new Js_traverse.share_constant)#program js in
      if times () then Format.eprintf "    share constant: %a@." Util.Timer.print t1;
      js
    else js in
  let js =
    if Option.Optim.compact_vardecl ()
    then
      let t2 = Util.Timer.make () in
      let js = (new Js_traverse.compact_vardecl)#program js in
      if times () then Format.eprintf "    compact var decl: %a@." Util.Timer.print t2;
      js
    else js in

  (* pack *)
  let use_strict js =
    if Option.Optim.strictmode ()
    then (J.Statement (J.Expression_statement (J.EStr ("use strict", `Utf8))), J.N) :: js
    else js in

  let global =
    J.ECall (
      J.EFun (None, [], [
          J.Statement (
            J.Return_statement(
              Some (J.EVar (J.S {J.name="this";var=None})))),
          J.N
        ], J.N), [], J.N) in

  let js =
    if not wrap_with_fun then
      let f =
        J.EFun (None, [J.S {J.name = global_object; var=None }], use_strict js,
                J.U) in
      [J.Statement (
        J.Expression_statement
          ((J.ECall (f, [global], J.N)))), J.N]
    else
      let f = J.EFun (None, [J.V (Code.Var.fresh ())], js, J.N) in
      [J.Statement (J.Expression_statement f), J.N] in

  (* post pack optim *)
  let t3 = Util.Timer.make () in
  let js = (new Js_traverse.simpl)#program js in
  if times () then Format.eprintf "    simpl: %a@." Util.Timer.print t3;
  let t4 = Util.Timer.make () in
  let js = (new Js_traverse.clean)#program js in
  if times () then Format.eprintf "    clean: %a@." Util.Timer.print t4;
  let js =
    if (Option.Optim.shortvar ())
    then
      let t5 = Util.Timer.make () in
      let keeps =
        if toplevel
        then StringSet.add global_object (Primitive.get_external ())
        else StringSet.empty in
      let keeps = StringSet.add "caml_get_global_data" keeps in
      let js = (new Js_traverse.rename_variable keeps)#program js in
      if times () then Format.eprintf "    shortten vars: %a@." Util.Timer.print t5;
      js
    else js in
  if times () then Format.eprintf "  optimizing: %a@." Util.Timer.print t;
  js



let configure formatter p =
  let pretty = Option.Optim.pretty () in
  Pretty_print.set_compact formatter (not pretty);
  Code.Var.set_pretty pretty;
  Code.Var.set_stable (Option.Optim.stable_var ());
  p

type profile = Code.program -> Code.program

let f ?(standalone=true) ?(wrap_with_fun=false) ?(profile=o1) ?toplevel ?linkall ?source_map formatter d =
  configure formatter >>
  print >>
  Effects.f >>
  profile >>
  deadcode' >>
  (* (fun (p, a) -> let fv = Freevars.f p in *)
  (*   Code.AddrMap.iter *)
  (*     (fun pc fv -> if Code.VarSet.cardinal fv > 0 then *)
  (*         Format.eprintf ">> %d: %d@." pc (Code.VarSet.cardinal fv)) *)
  (*     fv; *)
  (*   Format.eprintf " <<\n%!"; *)
  (*   (p, a)) >> *)

  generate d ?toplevel >>
  (fun p ->
     let fv = new Js_traverse.free in
     let _ = fv#program p in
     Code.VarSet.iter (fun v ->
       Format.fprintf Format.err_formatter "%a " Code.Var.print v
     ) (fv#get_free);
     Format.fprintf Format.err_formatter "<<\n%!";
     p) >>
  (fun p ->
     Js_output.program (Pretty_print.to_out_channel stdout) p;
     p) >>

  link ~standalone ?linkall >>

  pack ~wrap_with_fun ?toplevel >>

  coloring >>

  check_js ~standalone >>
  header formatter ~standalone >>
  output formatter ?source_map

let from_string prims s formatter =
  let (p,d) = Parse_bytecode.from_string prims s in
  f ~standalone:false ~wrap_with_fun:true formatter d p


let profiles = [0,o0;
                1,o1;
                2,o2;
                3,o3]
let profile i =
  try
    Some (List.assoc i profiles)
  with Not_found -> None
