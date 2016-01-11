(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2014 Hugo Heuzard
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

open Code
module J = Javascript
open Js_traverse
open Javascript


class tailcall = object(m)
  inherit map as super

  val mutable tc = VarSet.empty

  method expression e =
    match e with
    | EFun _ -> e
    | _ -> super#expression e

  method statement s =
    let s = super#statement s in
    match s with
    | Return_statement (Some e) ->
      ignore(m#last_e e);
      s

    | _ -> s

  method source s =
    match s with
    | Function_declaration _ -> s
    | Statement s -> Statement (m#statement s)

  method get = tc

  method clear = tc <- VarSet.empty

  method private last_e e =
    match e with
      | ECall (EVar (V var), _args, _) -> tc <- VarSet.add var tc
      | ESeq (_,e) -> m#last_e e
      | ECond (_,e1,e2) -> m#last_e e1;m#last_e e2
      | _ -> ()
end

class tailcall_rewrite f = object(m)
  inherit map as super
  method expression e =
    match e with
    | EFun _ -> e
    | _ -> super#expression e

  method statement s =
    let s = super#statement s in
    match s with
    | Return_statement(Some e) -> begin match m#last_e e with
        | None -> s
        | Some s -> s
      end
    | Suspended_statement thunk ->
      thunk ()
    | _ -> s

  method private last_e e =
    match e with
    | ECall (EVar var,args, _) -> f var args
    | ECond (cond,e1,e2) ->
      let e1' = m#last_e e1 in
      let e2' = m#last_e e2 in
      begin match e1',e2' with
        | None,None -> None
        | Some s,None ->
          Some (If_statement(cond,(s, N),Some (Return_statement (Some e2),N)))
        | None,Some s ->
          Some (If_statement(cond,(Return_statement (Some e1),N),Some (s, N)))
        | Some s1,Some s2 ->
          Some (If_statement(cond,(s1, N),Some (s2, N)))
      end
    | ESeq (e1,e2) ->
      begin match m#last_e e2 with
        | None -> None
        | Some s2 -> Some (Block ([(Expression_statement e1, N);(s2, N)]))
      end
    | _ -> None
  method source s =
    match s with
    | Statement st -> Statement (m#statement st)
    | Function_declaration _ -> s


end


module type TC = sig
  val rewrite :
    (Code.Var.t * Javascript.expression * J.location * VarSet.t * VarSet.t * bool) list ->
    (string -> Javascript.expression) -> Javascript.statement
end

module Ident : TC = struct
  let rewrite closures _get_prim =
    J.Variable_statement
       (List.map (fun (name, cl, loc, _, _, _) -> J.V name, Some (cl, loc))
          closures)

end

module While : TC = struct
  let rewrite _closures _get_prim = failwith "todo"
end

module Tramp : TC = struct

  let _m2old = ref VarMap.empty
  let m2new = ref VarMap.empty

  let counters = ref VarMap.empty

  let rewrite cls get_prim =
    let is_ident_rewrite x req_tc cont_tc =
      let tc = VarSet.union req_tc cont_tc in
      not (VarSet.mem x tc) &&
      not (VarMap.exists (fun v _ -> VarSet.mem v tc) !m2new)
    in

    match cls with
    | [x,_cl,_,req_tc,cont_tc,is_cont] when
        is_ident_rewrite x req_tc cont_tc ->
      Ident.rewrite cls get_prim
    | _ ->
    let counter = Var.fresh () in
    Var.name counter "counter";
    List.iter (fun (v,_,_,_,_,_) ->
      let v' = Var.fork v in
      _m2old := VarMap.add v' v !_m2old;
      m2new := VarMap.add v v' !m2new
    ) cls;
      
    let rewrite v args =
      try
        match v with
        | J.S _ -> None
        | J.V v ->
          let n = J.V (VarMap.find v !m2new) in
          let counter = VarMap.find v !counters in
          let st = J.Return_statement (
            Some (
              J.ECond (
                J.EBin (J.Lt,
                        J.EVar (J.V counter),
                        J.ENum (float_of_int (Option.Param.tailcall_max_depth ()))),
                J.ECall(J.EVar n, J.EBin (J.Plus,J.ENum 1.,J.EVar (J.V counter)) :: args,J.N),
                J.ECall (
                  get_prim "caml_trampoline_return",
                  [J.EVar n ; J.EArr (List.map (fun x -> Some x) (J.ENum 0. :: args))], J.N
                ))))
          in Some st
      with Not_found -> None
    in
    let rw = new tailcall_rewrite rewrite in

    let to_wrap, not_to_wrap = List.partition (fun (v,_,_,req_tc,cont_tc,_) ->
      let all_tc = VarSet.union req_tc cont_tc in
      (* A closure must be wrapped if:
         - some closure of [cls] (including itself) performs a
         tailcall to it;
         - if it performs a tailcall to some other closure of [cls]
         (so it has access to the counter). *)
      List.exists (fun (_, _, _, req_tc, cont_tc, _) ->
        VarSet.mem v req_tc || VarSet.mem v cont_tc
      ) cls
      || List.exists (fun (v', _, _, _, _, _) ->
        VarSet.mem v' all_tc
      ) cls
    ) cls in
        
    Printf.eprintf "counter: v%d " (Var.idx counter);
    Printf.eprintf "to_wrap:"; List.iter (fun (v,_,_,_,_,_) -> Printf.eprintf " v%d" (Var.idx v)) to_wrap;
    Printf.eprintf " not_to_wrap:"; List.iter (fun (v,_,_,_,_,_) -> Printf.eprintf " v%d" (Var.idx v)) not_to_wrap;
    Printf.eprintf "\n";
    
    counters := List.fold_left (fun counters (v,_,_,_,_,_) ->
      VarMap.add v counter counters) !counters to_wrap;
    let wrappers = List.map (fun (v,clo,_,_,_,_) ->
        match clo with
        | J.EFun (_, args, _, nid) ->
          let b = J.ECall(
              get_prim "caml_trampoline",
              [J.ECall(J.EVar (J.V (VarMap.find v !m2new)), J.ENum 0. :: List.map (fun i -> J.EVar i) args, J.N)], J.N) in
          let b = (J.Statement (J.Return_statement (Some b)), J.N) in
          v,J.EFun (None, args,[b],nid )
        | _ -> assert false) to_wrap in
    let reals = List.map (fun (v,clo,_,_,_,_) ->
        VarMap.find v !m2new,
        match clo with
        | J.EFun (nm,args,body,nid) ->
          J.EFun (nm,(J.V counter)::args,rw#sources body, nid)
        | _ -> assert false
      ) to_wrap in
    let not_wrapped = List.map (fun (v,clo,_,_,_,_) ->
      v,
      match clo with
      | J.EFun (nm,args,body,nid) ->
        J.EFun (nm,args,rw#sources body, nid)
      | _ -> assert false
    ) not_to_wrap in
      
    let make binds =
      J.Variable_statement
         (List.map (fun (name, ex) -> J.V (name), Some (ex, J.N)) binds) in
    let res =
      make (not_wrapped@reals@wrappers) in
    (* cleanup *)
    List.iter (fun (v,_,_,_,_,_) ->
      let v' = VarMap.find v !m2new in
      _m2old := VarMap.remove v' !_m2old;
      m2new := VarMap.remove v !m2new
    ) cls;
    res

end

let rewrite l =
  let open Option.Param in
  match tailcall_optim () with
  | TcNone -> Ident.rewrite l
  | TcTrampoline -> Tramp.rewrite l
  | TcWhile -> While.rewrite l

let ident_rewrite = Ident.rewrite
