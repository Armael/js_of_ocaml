open Code

let fresh2 () = Var.fresh (), Var.fresh ()
let fresh3 () = Var.fresh (), Var.fresh (), Var.fresh ()
let fresh4 () = Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh ()
let fresh5 () =
  Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh ()
let fresh6 () =
  Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (),
  Var.fresh ()

let add_block new_blocks block =
  let blocks, free_pc = !new_blocks in
  new_blocks := (AddrMap.add free_pc block blocks, free_pc + 1);
  free_pc

let closure_of_cont new_blocks params cont =
  let fresh_params = List.map (fun v -> (v, Var.fresh ())) params in
  let fresh_of v =
    try List.assoc v fresh_params with
    Not_found -> v in    

  let addr = add_block new_blocks {
    params = List.map fresh_of params;
    handler = None; 
    body = [];
    branch = Branch (fst cont, List.map fresh_of (snd cont));
  } in
  Closure (params, (addr, params))

let identity () =
  let x = Var.fresh () in
  { params = [x];
    handler = None; 
    body = [];
    branch = Return x;
  }

let toplevel_k () = identity ()

let toplevel_kf () =
  let x, x' = Var.fresh (), Var.fresh () in
  (* TODO *)
  { params = [x; x'];
    handler = None;
    body = [];
    branch = Return x;
  }

let alloc_stack_k hv k kf =
  let v, ret = Var.fresh (), Var.fresh () in
  { params = [v];
    handler = None;
    body = [Let (ret, Apply (hv, [k; kf; v], true))];
    branch = Return ret;
  }

let alloc_stack_kf hf k kf =
  let v, v', ret = Var.fresh (), Var.fresh (), Var.fresh () in
  { params = [v; v'];
    handler = None;
    body = [Let (ret, Apply (hf, [k; kf; v; v'], true))];
    branch = Return ret;
  }

let alloc_stack k kf =
  let f, x, ret = Var.fresh (), Var.fresh (), Var.fresh () in
  { params = [f; x];
    handler = None;
    body = [Let (ret, Apply (f, [k; kf; x], true))];
    branch = Return ret;
  }

let cps_alloc_stack
    new_blocks
    (ret: Var.t) (kf: Var.t)
    (hv: Var.t) (hf: Var.t) =
  let id, stack_k, stack_kf = fresh3 () in
  let f, v1, v2, v3, v4, v5 = fresh6 () in
  let id_addr = add_block new_blocks (identity ()) in
  let stack_k_addr = add_block new_blocks (alloc_stack_k hv id kf) in
  let stack_kf_addr = add_block new_blocks (alloc_stack_kf hf id kf) in
  let stack_addr = add_block new_blocks (alloc_stack stack_k stack_kf) in
  [Let (id, Closure ([v1], (id_addr, [v1])));
   Let (stack_k, Closure ([v2], (stack_k_addr, [v2])));
   Let (stack_kf, Closure ([v3; v4], (stack_kf_addr, [v3; v4])));
   Let (ret, Closure ([f; v5], (stack_addr, [f; v5])))]

let cps_last new_blocks (k: Var.t) (kf: Var.t) (last: last): instr list * last =
  let (@>) instrs1 (instrs2, last) = (instrs1 @ instrs2, last) in
  let cps_cont (pc, args) = (pc, k :: kf :: args) in
  let cps_return x =
    let kret = Var.fresh () in
    [Let (kret, Apply (k, [x], true))],
    Return kret
  in
  let cps_branch cont =
    [], Branch (cps_cont cont)
  in

  match last with
  | Return x ->
    cps_return x
  | Raise x ->
    (* TODO *)
    [], Raise x
  | Stop ->
    (* ??? *)
    [], Stop
  | Branch cont ->
    cps_branch cont
  | Cond (cond, x, cont1, cont2) ->
    [], Cond (cond, x, cps_cont cont1, cps_cont cont2)
  | Switch (x, c1, c2) ->
    [], Switch (x, Array.map cps_cont c1, Array.map cps_cont c2)
  | Pushtrap (cont1, x, cont2, pc) ->
    (* TODO *)
    [], Pushtrap (cps_cont cont1, x, cps_cont cont2, pc)
  | Poptrap cont ->
    (* TODO *)
    [], Poptrap (cps_cont cont)
  | Resume (ret, (stack, func, args), cont_opt) ->
    [Let (ret, Apply (stack, [func; args], true))] @>
    begin match cont_opt with
      | None ->
        cps_return ret
      | Some cont ->
        cps_branch cont
    end
  | Perform (ret, eff, cont) ->
    let cur_k, cur_stack = fresh2 () in
    let f, v = fresh2 () in
    let kfret = Var.fresh () in
    let cur_k_closure = closure_of_cont new_blocks [ret] (cps_cont cont) in
    let stack = add_block new_blocks (alloc_stack cur_k kf) in
    [Let (cur_k, cur_k_closure);
     Let (cur_stack, Closure ([f; v], (stack, [f; v])));
     Let (kfret, Apply (kf, [eff; cur_stack], true))],
    Return kfret
  | Delegate (eff, stack) ->
    let kfret = Var.fresh () in
    [Let (kfret, Apply (kf, [eff; stack], true))],
    Return kfret
  | LastApply (ret, (f, args, full), cont_opt) ->
    begin match cont_opt with
      | None ->
        [Let (ret, Apply (f, k :: kf :: args, full))],
        Return ret
      | Some cont ->
        let cur_k = Var.fresh () in
        let cur_k_closure = closure_of_cont new_blocks [ret] (cps_cont cont) in
        let ret' = Var.fresh () in
        [Let (cur_k, cur_k_closure);
         Let (ret', Apply (f, cur_k :: kf :: args, full))],
        Return ret'
    end

let cps_instr new_blocks (kf: Var.t) (instr: instr): instr list =
  match instr with
  | Let (x, Prim (Extern "caml_alloc_stack", [Pv hv; Pv _; Pv hf])) ->
    (* TODO [he] *)
    cps_alloc_stack new_blocks x kf hv hf
  | Let (x, Prim (Extern "caml_bvar_create", [Pv y]))
  | Let (x, Prim (Extern "caml_bvar_take", [Pv y])) ->
    (* TODO *)
    let id, v = fresh2 () in
    let id_addr = add_block new_blocks (identity ()) in
    [Let (id, Closure ([v], (id_addr, [v])));
     Let (x, Apply (id, [y], true))]
  | Let (x, Closure (params, (pc, args))) ->
    let k, kf = fresh2 () in
    [Let (x, Closure (k :: kf :: params, (pc, k :: kf :: args)))]
  | Let (_, Apply _) ->
    assert false
  | _ ->
    [instr]

let cps_blocks new_blocks blocks =
  AddrMap.map (fun block ->
    let k, kf = fresh2 () in
    let instrs, last = cps_last new_blocks k kf block.branch in
    let handler = match block.handler with
      | None -> None
      | Some (v, (addr, params)) -> Some (v, (addr, k::kf::params)) in
    { params = k :: kf :: block.params;
      handler;
      body = (List.map (cps_instr new_blocks kf) block.body
              |> List.flatten)
             @ instrs;
      branch = last }
  ) blocks

let f ((start, blocks, free_pc): Code.program): Code.program =
  let new_blocks = ref (AddrMap.empty, free_pc) in
  
  let blocks = cps_blocks new_blocks blocks in
  let k, kf = fresh2 () in
  let v1, v2, v3 = fresh3 () in
  let toplevel_k_addr = add_block new_blocks (toplevel_k ()) in
  let toplevel_kf_addr = add_block new_blocks (toplevel_kf ()) in
  let new_start = add_block new_blocks {
    params = [];
    handler = None;
    body = [
      Let (k, Closure ([v1], (toplevel_k_addr, [v1])));
      Let (kf, Closure ([v2; v3], (toplevel_kf_addr, [v2; v3])))
    ];
    branch = Branch (start, [k; kf])
  } in
  let new_blocks, free_pc = !new_blocks in
  let blocks = AddrMap.merge
      (fun _ b b' ->
         match (b, b') with
         | None,   None   -> None
         | Some b, None
         | None,   Some b -> Some b
         | _ -> assert false)
      blocks new_blocks in
  (new_start, blocks, free_pc)
