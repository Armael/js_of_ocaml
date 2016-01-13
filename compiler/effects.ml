open Util
open Code

type graph = {
  root  : addr;
  succs : AddrSet.t IntMap.t;
  backs : AddrSet.t IntMap.t;
  preds : AddrSet.t IntMap.t;
  loops : AddrSet.t;
}

let get_values k map =
  try IntMap.find k map with Not_found -> AddrSet.empty
  
let add_value k v map =
  let vs = get_values k map in
  IntMap.add k (AddrSet.add v vs) map

let build_graph (blocks: block AddrMap.t) (pc: addr): graph =
  let rec loop (g: graph) (pc: addr) (visited: AddrSet.t) (anc: AddrSet.t) =
    if not (AddrSet.mem pc visited) then begin
      let visited = AddrSet.add pc visited in
      let anc = AddrSet.add pc anc in
      let s = Code.fold_children blocks pc AddrSet.add AddrSet.empty in
      let backs = AddrSet.inter s anc in

      let succs = AddrSet.filter (fun pc -> not (AddrSet.mem pc anc)) s in
      let preds =
        AddrSet.fold (fun succ preds -> add_value succ pc preds)
          succs g.preds
        |> AddrSet.fold (fun back preds -> add_value back pc preds)
          backs
      in
      let loops = AddrSet.fold AddrSet.add backs g.loops in

      let g = { g with
                backs = AddrMap.add pc backs g.backs;
                succs = AddrMap.add pc succs g.succs;
                preds;
                loops;
              } in
      AddrSet.fold (fun pc' (g, visited) -> loop g pc' visited anc)
        succs (g, visited)
    end else (g, visited)
  in

  let (g, _) =
    loop
      { root = pc;
        succs = IntMap.empty;
        backs = IntMap.empty;
        preds = IntMap.empty;
        loops = AddrSet.empty; }
      pc AddrSet.empty AddrSet.empty in
  g

let print_graph (g: graph) =
  Printf.eprintf "digraph G {\n";
  IntMap.iter (fun k s ->
    AddrSet.iter (fun v ->
      Printf.eprintf "%d -> %d;\n" k v
    ) s
  ) g.succs;

  IntMap.iter (fun k s ->
    AddrSet.iter (fun v ->
      Printf.eprintf "%d -> %d [style=dashed,color=red];\n" k v
    ) s
  ) g.backs;

   (* IntMap.iter (fun k s -> *)
   (*   AddrSet.iter (fun v -> *)
   (*     Printf.eprintf "%d -> %d [style=dashed,color=blue];\n" k v *)
   (*   ) s *)
   (* ) g.preds; *)

   Printf.eprintf "}\n"

let dominated_by_node (g: graph): AddrSet.t IntMap.t =
  let explore_avoiding v =
    let rec loop node visited =
      let visited = AddrSet.add node visited in
      try
        let succs = AddrSet.diff (IntMap.find node g.succs) visited in
        AddrSet.fold loop succs visited
      with Not_found ->
        visited
    in
    loop g.root (AddrSet.singleton v)
  in

  let all_nodes =
    IntMap.fold (fun v _ s -> AddrSet.add v s)
      g.preds (AddrSet.singleton g.root) in

  IntMap.fold (fun v _ dominated_by ->
    let not_dominated = explore_avoiding v in
    IntMap.fold (fun v' _ dominated_by ->
      if not (AddrSet.mem v' not_dominated) then
        add_value v v' dominated_by
      else
        dominated_by
    ) g.preds dominated_by
  ) g.preds (IntMap.singleton g.root all_nodes)

let immediate_dominator_of_node (g: graph): addr IntMap.t =
  let dominated_by = dominated_by_node g in
  let dom_by node = get_values node dominated_by in

  let rec loop node (idom: addr IntMap.t) =
    let dom = dom_by node |> AddrSet.remove node in
    let dom_dom =
      AddrSet.fold
        (fun node' dom_dom ->
           dom_by node'
           |> AddrSet.remove node'
           |> AddrSet.union dom_dom)
        dom AddrSet.empty
    in
    let idom_node = AddrSet.diff dom dom_dom in
    let idom = AddrSet.fold (fun node' idom ->
      IntMap.add node' node idom) idom_node idom in
    AddrSet.fold loop idom_node idom
  in
  loop g.root IntMap.empty

type jump_closures = {
  closure_of_jump : Var.t IntMap.t;
  closure_of_alloc_site : (Var.t * addr) list IntMap.t;
  allocated_call_blocks : (Var.t, addr) Hashtbl.t;
}

let empty_jump_closures = {
  closure_of_jump = IntMap.empty;
  closure_of_alloc_site = IntMap.empty;
  allocated_call_blocks = Hashtbl.create 3;
}

let jump_closures (g: graph): jump_closures =
  let idom = immediate_dominator_of_node g in
  let closure_of_jump, closure_of_alloc_site =
    IntMap.fold (fun node preds (c_o_b, c_o_a_s) ->
      if AddrSet.cardinal preds >= 2 then
        let cname = Var.fresh () in
        let idom_node = IntMap.find node idom in
        let closures_to_allocate =
          try IntMap.find idom_node c_o_a_s
          with Not_found -> [] in
        
        (IntMap.add node cname c_o_b,
         IntMap.add idom_node ((cname, node) :: closures_to_allocate)
           c_o_a_s)
      else
        (c_o_b, c_o_a_s)
    ) g.preds (IntMap.empty, IntMap.empty) in

  { closure_of_jump; closure_of_alloc_site;
    allocated_call_blocks = Hashtbl.create 37 }

let merge_jump_closures jc1 jc2 =
  let m _ a b = 
    match (a, b) with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false in
  { closure_of_jump =
      IntMap.merge m jc1.closure_of_jump jc2.closure_of_jump;
    closure_of_alloc_site =
      IntMap.merge m jc1.closure_of_alloc_site jc2.closure_of_alloc_site;
    allocated_call_blocks =
      (* TODO *)
      Hashtbl.create 3
  }

(******************************************************************************)

let cont_closures = ref VarSet.empty
let is_cont_closure v = VarSet.mem v !cont_closures

(******************************************************************************)

type st = {
  mutable new_blocks : Code.block AddrMap.t * Code.addr;
  blocks : Code.block AddrMap.t;
  jc : jump_closures;
}

let fresh2 () = Var.fresh (), Var.fresh ()
let fresh3 () = Var.fresh (), Var.fresh (), Var.fresh ()
let fresh4 () = Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh ()
let fresh5 () =
  Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh ()
let fresh6 () =
  Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (),
  Var.fresh ()

let add_block st block =
  let blocks, free_pc = st.new_blocks in
  st.new_blocks <- (AddrMap.add free_pc block blocks, free_pc + 1);
  free_pc

let filter_cont_params st cont =
  let block = AddrMap.find (fst cont) st.blocks in
  let cont_params = snd cont in
  let block_params = block.params in
  let rec loop = function
    | x::xs, y::ys -> x :: loop (xs, ys)
    | _, [] -> []
    | [], _ -> assert false in
  (fst cont, loop (cont_params, block_params))

let add_call_block st cname params =
  let fresh_params = List.map (fun _ -> Var.fresh ()) params in
  let ret = Var.fresh () in
  let addr = add_block st {
    params = fresh_params;
    handler = None;
    body = [Let (ret, Apply (cname, params, false))];
    branch = Return ret
  } in
  Hashtbl.add st.jc.allocated_call_blocks cname addr;
  addr

let cps_branch st k kf cont =
  let cont = filter_cont_params st cont in
  let caddr = fst cont in
  let params = k :: kf :: snd cont in
  try
    let cname = IntMap.find caddr st.jc.closure_of_jump in
    Printf.eprintf "cps_branch: %d ~> call v%d params:" caddr (Var.idx cname);
    List.iter (fun v -> Printf.eprintf " v%d" (Var.idx v)) params;
    Printf.eprintf "\n\n";
    let ret = Var.fresh () in
    [Let (ret, Apply (cname, params, false))],
    Return ret
  with Not_found ->
    [], Branch (caddr, params)

let closure_of_cont st params k kf cont =
  let name = Var.fresh () in
  cont_closures := VarSet.add name !cont_closures;
  let fresh_params = List.map (fun v -> (v, Var.fresh ())) params in
  let fresh_of v =
    try List.assoc v fresh_params with
      Not_found -> v in

  let body, branch =
    cps_branch st k kf (fst cont, List.map fresh_of (snd cont))
  in

  let addr = add_block st {
    params = List.map fresh_of params;
    handler = None; 
    body; branch;
  } in
  (name, Closure (params, (addr, params)))

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
    st
    (ret: Var.t) (kf: Var.t)
    (hv: Var.t) (hf: Var.t) =
  let id, stack_k, stack_kf = fresh3 () in
  let f, v1, v2, v3, v4, v5 = fresh6 () in
  let id_addr = add_block st (identity ()) in
  let stack_k_addr = add_block st (alloc_stack_k hv id kf) in
  let stack_kf_addr = add_block st (alloc_stack_kf hf id kf) in
  let stack_addr = add_block st (alloc_stack stack_k stack_kf) in
  [Let (id, Closure ([v1], (id_addr, [v1])));
   Let (stack_k, Closure ([v2], (stack_k_addr, [v2])));
   Let (stack_kf, Closure ([v3; v4], (stack_kf_addr, [v3; v4])));
   Let (ret, Closure ([f; v5], (stack_addr, [f; v5])))]

let cps_last st (k: Var.t) (kf: Var.t) (last: last): instr list * last =
  let (@>) instrs1 (instrs2, last) = (instrs1 @ instrs2, last) in
  let cps_cont (pc, args) = (pc, k :: kf :: args) in
  let cps_jump_cont cont =
    let pc, args = filter_cont_params st cont in
    let args = k :: kf :: args in
    try
      let cname = IntMap.find pc st.jc.closure_of_jump in
      let call_block = add_call_block st cname args in
      (call_block, args)
    with Not_found ->
      (pc, args)
  in
  
  let cps_return x =
    let kret = Var.fresh () in
    [Let (kret, Apply (k, [x], true))],
    Return kret
  in

  let cps_branch = cps_branch st k kf in
  let closure_of_cont params = closure_of_cont st params k kf in

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
    [], Cond (cond, x, cps_jump_cont cont1, cps_jump_cont cont2)
  | Switch (x, c1, c2) ->
    [], Switch (x, Array.map cps_jump_cont c1, Array.map cps_jump_cont c2)
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
    let cur_stack = Var.fresh () in
    let f, v = fresh2 () in
    let kfret = Var.fresh () in
    let cur_k, cur_k_closure = closure_of_cont [ret] cont in
    let stack = add_block st (alloc_stack cur_k kf) in
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
        let cur_k, cur_k_closure = closure_of_cont [ret] cont in
        let ret' = Var.fresh () in
        [Let (cur_k, cur_k_closure);
         Let (ret', Apply (f, cur_k :: kf :: args, full))],
        Return ret'
    end

let cps_instr st (kf: Var.t) (instr: instr): instr list =
  match instr with
  | Let (x, Prim (Extern "caml_alloc_stack", [Pv hv; Pv _; Pv hf])) ->
    (* TODO [he] *)
    cps_alloc_stack st x kf hv hf
  | Let (x, Prim (Extern "caml_bvar_create", [Pv y]))
  | Let (x, Prim (Extern "caml_bvar_take", [Pv y])) ->
    (* TODO *)
    let id, v = fresh2 () in
    let id_addr = add_block st (identity ()) in
    [Let (id, Closure ([v], (id_addr, [v])));
     Let (x, Apply (id, [y], true))]
  | Let (x, Closure (params, (pc, args))) ->
    let k, kf = fresh2 () in
    [Let (x, Closure (k :: kf :: params, (pc, k :: kf :: args)))]
  | Let (_, Apply _) ->
    assert false
  | _ ->
    [instr]

let cps_block st block_addr block =
  let k, kf = fresh2 () in
  let handler = match block.handler with
    | None -> None
    | Some (v, (addr, params)) -> Some (v, (addr, k::kf::params)) in

  let alloc_jump_closure =
    try
      let to_allocate = IntMap.find block_addr st.jc.closure_of_alloc_site in
      List.map (fun (cname, jump_addr) ->
        let jump_block = IntMap.find jump_addr st.blocks in
        let k, kf = fresh2 () in
        let fresh_params =
          k :: kf :: List.map (fun _ -> Var.fresh ()) jump_block.params in
        Let (cname, Closure (fresh_params, (jump_addr, fresh_params)))
      ) to_allocate
    with Not_found ->
      []
  in

  let last_instrs, last = cps_last st k kf block.branch in

  let body =
    (List.map (cps_instr st kf) block.body
     |> List.flatten)
    @ alloc_jump_closure
    @ last_instrs in
  
  { params = k :: kf :: block.params;
    handler;
    body;
    branch = last }

let cps_blocks st =
  AddrMap.mapi (cps_block st) st.blocks

let nop_block block =
  let nop_last = function
    | LastApply (ret, (f, args, full), cont_opt) ->
      [Let (ret, Apply (f, args, full))],
      begin match cont_opt with
        | None -> Return ret
        | Some cont -> Branch cont
      end
    | last -> [], last in
  let add_instr, branch = nop_last block.branch in
  { block with
    branch;
    body = block.body @ add_instr }

let nop (start, blocks, free_pc) =
  let g = build_graph blocks start in
  print_graph g;

  Printf.eprintf "\nidom:\n";

  let idom = immediate_dominator_of_node g in
  IntMap.iter (fun node dom ->
    Printf.eprintf "%d -> %d\n" node dom;
  ) idom;

  Printf.eprintf "\n";
  
  let blocks = AddrMap.map nop_block blocks in
  (start, blocks, free_pc)

let f ((start, blocks, free_pc): Code.program): Code.program =
  let jc : jump_closures =
    Code.fold_closures (start, blocks, free_pc)
      (fun _ _ (start, _) jc ->
         Printf.eprintf ">> Start: %d\n\n" start;
         let cfg = build_graph blocks start in

         print_graph cfg; Printf.eprintf "%!";

         let closure_jc = jump_closures cfg in

         Printf.eprintf "\nidom:\n";

         let idom = immediate_dominator_of_node cfg in
         IntMap.iter (fun node dom ->
           Printf.eprintf "%d -> %d\n" node dom;
         ) idom;

         Printf.eprintf "\nClosure of alloc site:\n";
         IntMap.iter (fun block to_allocate ->
           List.iter (fun (cname, caddr) ->
             Printf.eprintf "%d -> v%d, %d\n" block (Var.idx cname) caddr;
           ) to_allocate
         ) closure_jc.closure_of_alloc_site;

         Printf.eprintf "\nClosure of jump:\n";
         IntMap.iter (fun block cname ->
           Printf.eprintf "%d -> v%d\n" block (Var.idx cname);
         ) closure_jc.closure_of_jump;
         Printf.eprintf "\n";

         merge_jump_closures closure_jc jc
      ) empty_jump_closures
  in

  let st = { new_blocks = AddrMap.empty, free_pc; blocks; jc } in
  let blocks = cps_blocks st in

  Printf.eprintf "Cont closures:";
  VarSet.iter (fun c -> Printf.eprintf " v%d" (Var.idx c)) !cont_closures;
  Printf.eprintf "\n\n%!";

  let k, kf = fresh2 () in
  let v1, v2, v3 = fresh3 () in
  let toplevel_k_addr = add_block st (toplevel_k ()) in
  let toplevel_kf_addr = add_block st (toplevel_kf ()) in
  let new_start = add_block st {
    params = [];
    handler = None;
    body = [
      Let (k, Closure ([v1], (toplevel_k_addr, [v1])));
      Let (kf, Closure ([v2; v3], (toplevel_kf_addr, [v2; v3])))
    ];
    branch = Branch (start, [k; kf])
  } in
  let new_blocks, free_pc = st.new_blocks in
  let blocks = AddrMap.merge
      (fun _ b b' ->
         match (b, b') with
         | None,   None   -> None
         | Some b, None
         | None,   Some b -> Some b
         | _ -> assert false)
      blocks new_blocks in
  (new_start, blocks, free_pc)
