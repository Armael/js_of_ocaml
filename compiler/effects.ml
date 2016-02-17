open Util
open Code

type graph = {
  root  : addr;
  succs : AddrSet.t AddrMap.t;
  backs : AddrSet.t AddrMap.t;
  preds : AddrSet.t AddrMap.t;
  loops : AddrSet.t;
  handler_succ : addr AddrMap.t;
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
      let handler_succ = match (AddrMap.find pc blocks).handler with
        | None -> g.handler_succ
        | Some (_, (handler_addr, _)) ->
          AddrMap.add pc handler_addr g.handler_succ in

      let g = { g with
                backs = AddrMap.add pc backs g.backs;
                succs = AddrMap.add pc succs g.succs;
                preds;
                loops;
                handler_succ;
              } in
      AddrSet.fold (fun pc' (g, visited) -> loop g pc' visited anc)
        succs (g, visited)
    end else (g, visited)
  in

  let (g, _) =
    loop
      { root = pc;
        succs = AddrMap.empty;
        backs = AddrMap.empty;
        preds = AddrMap.empty;
        loops = AddrSet.empty;
        handler_succ = AddrMap.empty;
      }
      pc AddrSet.empty AddrSet.empty in
  g

let print_graph blocks (g: graph) =
  let is_handler_succ v v' =
    match (AddrMap.find v blocks).handler with
    | None -> false
    | Some (_, (pc, _)) -> pc = v'
  in
  
  Printf.eprintf "digraph G {\n";
  IntMap.iter (fun k s ->
    AddrSet.iter (fun v ->
      if is_handler_succ k v then
        Printf.eprintf "%d -> %d [style=dashed,color=green];\n" k v
      else
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

  AddrSet.fold (fun v dominated_by ->
    let not_dominated = explore_avoiding v in
    IntMap.fold (fun v' _ dominated_by ->
      if not (AddrSet.mem v' not_dominated) then
        add_value v v' dominated_by
      else
        dominated_by
    ) g.preds dominated_by
  ) all_nodes (IntMap.singleton g.root all_nodes)

let dominance_frontier (g: graph) dominated_by node0 =
  let dom_by_node0 =
    try AddrMap.find node0 dominated_by with
      Not_found -> AddrSet.empty in
    let rec loop node frontier =
      try
        let succs =
          AddrMap.find node g.succs
          |> (fun succs ->
            try AddrSet.remove (AddrMap.find node g.handler_succ) succs
            with Not_found -> succs)
        in
        AddrSet.fold (fun node' frontier ->
          if AddrSet.mem node' dom_by_node0 then
            loop node' frontier
          else
            AddrSet.add node' frontier
        ) succs frontier
      with Not_found ->
        frontier in
    loop node0 AddrSet.empty
    
  

type trywith_exit_nodes = {
  entry_of_exit : AddrSet.t AddrMap.t;
  exit_of_entry : addr option AddrMap.t;
}

let empty_exit_nodes = {
  entry_of_exit = AddrMap.empty;
  exit_of_entry = AddrMap.empty;
}

let trywith_exit_nodes
    (blocks: block AddrMap.t)
    (g: graph)    
    dominated_by
  :
  trywith_exit_nodes
  =
  let rec loop node (entry_of_exit, exit_of_entry, visited) =
    let add_entry exit entry entry_of_exit =
      let entries = try AddrMap.find exit entry_of_exit with Not_found -> AddrSet.empty in
      AddrMap.add exit (AddrSet.add entry entries) entry_of_exit in
    let visited = AddrSet.add node visited in
    try
      let succs = AddrSet.diff (IntMap.find node g.succs) visited in
      match (AddrMap.find node blocks).branch with
      | Pushtrap ((_, _), _, (pc2, _), _) ->
        Printf.eprintf "%d ==> dominance frontier of %d\n" node pc2;
        let frontier = dominance_frontier g dominated_by pc2 in
        Printf.eprintf "frontier:";
        AddrSet.iter (fun node -> Printf.eprintf " %d" node) frontier;
        Printf.eprintf "\n";
        assert (AddrSet.cardinal frontier <= 1);
        let entry_of_exit, exit_of_entry =
          if AddrSet.is_empty frontier then
            entry_of_exit,
            AddrMap.add node None exit_of_entry
          else
            let exit = AddrSet.choose frontier in
            add_entry exit node entry_of_exit,
            AddrMap.add node (Some exit) exit_of_entry in
        AddrSet.fold loop succs (entry_of_exit, exit_of_entry, visited)
      | _ ->
        AddrSet.fold loop succs (entry_of_exit, exit_of_entry, visited)
    with Not_found ->
      (entry_of_exit, exit_of_entry, visited)
  in

  let entry_of_exit, exit_of_entry, _ =
    loop g.root (AddrMap.empty, AddrMap.empty, AddrSet.empty) in
  { entry_of_exit; exit_of_entry }

let merge_exit_nodes en1 en2 =
  let m _ a b = 
    match (a, b) with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false in
  { entry_of_exit = AddrMap.merge m en1.entry_of_exit en2.entry_of_exit;
    exit_of_entry = AddrMap.merge m en1.exit_of_entry en2.exit_of_entry;
  }

let delimited_by blocks g exit_nodes : AddrSet.t AddrMap.t =
  let rec loop
      (pc: addr)
      (visited: AddrSet.t)
      (delimited_by_acc: AddrSet.t)
      (delimited_by: AddrSet.t AddrMap.t)
    =
    if not (AddrSet.mem pc visited) then begin
      let visited = AddrSet.add pc visited in
      let delimited_by_acc = AddrSet.remove pc delimited_by_acc in
      let delimited_by = AddrMap.add pc delimited_by_acc delimited_by in

      let block = AddrMap.find pc blocks in
      let delimited_by_acc =
        match block.branch with
        | Pushtrap _ ->
          begin match AddrMap.find pc exit_nodes.exit_of_entry with
            | None -> delimited_by_acc
            | Some exit_node -> AddrSet.add exit_node delimited_by_acc
          end
        | _ -> delimited_by_acc in
      AddrSet.fold (fun pc' (visited, delimited_by) ->
        loop pc' visited delimited_by_acc delimited_by)
        (AddrMap.find pc g.succs)
        (visited, delimited_by)
    end else
      (visited, delimited_by)
  in
  let (_, d) = loop g.root AddrSet.empty AddrSet.empty AddrMap.empty in
  d

let merge_delimited_by d1 d2 =
  let m _ a b = 
    match (a, b) with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false in
  AddrMap.merge m d1 d2

let defs_of_exit_scope blocks g exit_nodes :
  (Flow.def array * Var.t VarMap.t) AddrMap.t =
  let rec loop
      (pc: addr)
      (visited: AddrSet.t)
      accs_of_open_scopes
      (defs_of_exit_scopes: (Flow.def array * Var.t VarMap.t) AddrMap.t)
    =
    let accs_of_open_scopes, defs_of_exit_scopes =
      try
        let ((_, _, d), entry_defs) =
          AddrMap.find pc accs_of_open_scopes in
        AddrMap.remove pc accs_of_open_scopes,
        AddrMap.add pc (d, entry_defs) defs_of_exit_scopes
      with Not_found ->
        accs_of_open_scopes, defs_of_exit_scopes in

    if not (AddrSet.mem pc visited) then begin
      let visited = AddrSet.add pc visited in
      let block = AddrMap.find pc blocks in

      let accs_of_open_scopes =
        AddrMap.map (fun (acc, d) -> (Flow.f_block ~acc blocks block, d))
          accs_of_open_scopes in

      let accs_of_open_scopes =
        match block.branch with
        | Pushtrap ((pc1, params1), _, (pc2, params2), _) ->
          begin match AddrMap.find pc exit_nodes.exit_of_entry with
            | None -> accs_of_open_scopes
            | Some exit_node ->
              let block1 = AddrMap.find pc1 blocks in
              let block2 = AddrMap.find pc2 blocks in
              let defsl =
                (List.combine block1.params params1) @
                (List.combine block2.params params2) in
              let entry_defs = List.fold_left (fun m (k, v) ->
                VarMap.add k v m) VarMap.empty defsl in
              
              (* todo: fixme: ugly *)
              let empty_acc =
                let nv = Var.count () in
                (VarISet.empty (),
                 Array.make nv VarSet.empty,
                 Array.make nv (Flow.Phi VarSet.empty)) in
              
              AddrMap.add exit_node (empty_acc, entry_defs) accs_of_open_scopes
          end
        | _ -> accs_of_open_scopes in

      AddrSet.fold (fun pc' (visited, defs_of_exit_scopes) ->
        loop pc' visited accs_of_open_scopes defs_of_exit_scopes)
        (AddrMap.find pc g.succs)
        (visited, defs_of_exit_scopes)
    end else
      (visited, defs_of_exit_scopes)
  in
  let (_, d) = loop g.root AddrSet.empty AddrMap.empty AddrMap.empty in
  d

let merge_defs_of_exit_scope d1 d2 =
  let m _ a b = 
    match (a, b) with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false in
  AddrMap.merge m d1 d2

let rec in_this_scope scope_defs v =
  let v = Var.idx v in
  match scope_defs.(v) with
  | Flow.Phi s -> VarSet.exists (in_this_scope scope_defs) s
  | Flow.Expr _ | Flow.FromOtherStack -> true
  | Flow.Param -> assert false

let rec entry_def_of scope_defs entry_defs v =
  try VarMap.find v entry_defs
  with Not_found ->
    let id = Var.idx v in
    match scope_defs.(id) with
    | Flow.Phi s ->
      let s' = VarSet.fold (fun v' s' ->
        VarSet.add (entry_def_of scope_defs entry_defs v') s')
        s VarSet.empty in
      assert (VarSet.cardinal s' = 1);
      VarSet.choose s'
    | _ -> assert false

let immediate_dominator_of_node (g: graph) dominated_by: addr AddrMap.t =
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

let jump_closures (g: graph) dominated_by: jump_closures =
  let idom = immediate_dominator_of_node g dominated_by in
  let closure_of_jump, closure_of_alloc_site
    =
    let non_handler_jumps node preds =
      AddrSet.cardinal @@
      AddrSet.filter (fun pred ->
        try AddrMap.find pred g.handler_succ <> node
        with Not_found -> true
      ) preds in
    
    IntMap.fold (fun node preds (c_o_j, c_o_a_s) ->
      if non_handler_jumps node preds >= 2 then
        let cname = Var.fresh () in
        let idom_node = IntMap.find node idom in
            let closures_to_allocate =
              try IntMap.find idom_node c_o_a_s
              with Not_found -> [] in
            let c_o_j = IntMap.add node cname c_o_j in
            let c_o_a_s =
              IntMap.add idom_node ((cname, node) :: closures_to_allocate)
                c_o_a_s in
            (c_o_j, c_o_a_s)
      else (c_o_j, c_o_a_s)
    ) g.preds
      (IntMap.empty, IntMap.empty) in

  { closure_of_jump; closure_of_alloc_site;
    allocated_call_blocks = Hashtbl.create 37; }

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
      Hashtbl.create 3;
  }

(******************************************************************************)

let cont_closures = ref VarSet.empty
let is_cont_closure v = VarSet.mem v !cont_closures

let alloc_stack_vars = ref VarSet.empty

(******************************************************************************)

type st = {
  mutable new_blocks : Code.block AddrMap.t * Code.addr;
  blocks : Code.block AddrMap.t;
  jc : jump_closures;
  en : trywith_exit_nodes;
  delimited_by : AddrSet.t AddrMap.t;
  defs_of_exit_node : (Flow.def array * Var.t VarMap.t) AddrMap.t;
  mutable kx_of_poptrap : Var.t AddrMap.t;
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
    | x::xs, _y::ys -> x :: loop (xs, ys)
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

let cps_branch st pc k kx kf cont =
  let cont = filter_cont_params st cont in
  let caddr = fst cont in
  let params = k :: kx :: kf :: snd cont in
  try
    let delim_by = AddrMap.find pc st.delimited_by in
    if not (AddrSet.mem caddr delim_by) then raise Not_found;
    Printf.eprintf "Translated a jump frow %d to %d into a return\n" pc caddr;
    let (scope_defs, _) = AddrMap.find caddr st.defs_of_exit_node in
    let l = List.filter (in_this_scope scope_defs) (snd cont) in
    assert (List.length l = 1);
    let interesting_param = List.hd l in
    [], Return interesting_param
  with Not_found ->
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

let closure_of_cont st pc params k kx kf cont =
  let name = Var.fresh () in
  cont_closures := VarSet.add name !cont_closures;
  let fresh_params = List.map (fun v -> (v, Var.fresh ())) params in
  let fresh_of v =
    try List.assoc v fresh_params with
      Not_found -> v in

  let body, branch =
    cps_branch st pc k kx kf (fst cont, List.map fresh_of (snd cont))
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

let toplevel_kx () =
  let x = Var.fresh () in
  { params = [x];
    handler = None;
    body = [];
    branch = Raise x;
  }

let toplevel_kf () =
  let x, x' = Var.fresh (), Var.fresh () in
  let ret = Var.fresh () in
  { params = [x; x'];
    handler = None;
    body = [Let (ret, Prim (Extern "caml_unhandled_effect", [Pv x]))];
    branch = Return ret;
  }

let alloc_stack_k hv k kx kf =
  let v, ret = Var.fresh (), Var.fresh () in
  { params = [v];
    handler = None;
    body = [Let (ret, Apply (hv, [k; kx; kf; v], true))];
    branch = Return ret;
  }

let alloc_stack_kx hx k kx kf = alloc_stack_k hx k kx kf

let alloc_stack_kf hf k kx kf =
  let v, v', ret = Var.fresh (), Var.fresh (), Var.fresh () in
  { params = [v; v'];
    handler = None;
    body = [Let (ret, Apply (hf, [k; kx; kf; v; v'], true))];
    branch = Return ret;
  }

let alloc_stack k kx kf =
  let f, x, ret = Var.fresh (), Var.fresh (), Var.fresh () in
  let body =
    (* let ret' = Var.fresh () in *)
    (* if tramp then *)
    (*   [Let (ret', Apply (f, [k; kx; kf; x], true)); *)
    (*    Let (ret, Prim (Extern "caml_trampoline", [Pv ret']))] *)
    (* else *)
      [Let (ret, Apply (f, [k; kx; kf; x], true))]
  in
  { params = [f; x];
    handler = None;
    body;
    branch = Return ret;
  }

let cps_alloc_stack
    st
    (ret: Var.t) (kx: Var.t) (kf: Var.t)
    (hv: Var.t) (hx: Var.t) (hf: Var.t) =
  let id, stack_k, stack_kx, stack_kf = fresh4 () in
  let f = Var.fresh () in
  let v1, v2, v3, v4, v5, v6 = fresh6 () in
  let id_addr = add_block st (identity ()) in
  let stack_k_addr = add_block st (alloc_stack_k hv id kx kf) in
  let stack_kx_addr = add_block st (alloc_stack_kx hx id kx kf) in
  let stack_kf_addr = add_block st (alloc_stack_kf hf id kx kf) in
  let stack_addr =
    add_block st (alloc_stack stack_k stack_kx stack_kf) in
  [Let (id, Closure ([v1], (id_addr, [v1])));
   Let (stack_k, Closure ([v2], (stack_k_addr, [v2])));
   Let (stack_kx, Closure ([v3], (stack_kx_addr, [v3])));
   Let (stack_kf, Closure ([v4; v5], (stack_kf_addr, [v4; v5])));
   Let (ret, Closure ([f; v6], (stack_addr, [f; v6])))]

let cps_last
    st
    (k: Var.t) (kx: Var.t) (kf: Var.t)
    (block_addr: addr) (last: last):
  instr list * last =
  let (@>) instrs1 (instrs2, last) = (instrs1 @ instrs2, last) in
  let cps_jump_cont cont =
    let pc, args = filter_cont_params st cont in
    let args = k :: kx :: kf :: args in
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

  let cps_branch' = cps_branch st block_addr k kx kf in
  let closure_of_cont' params = closure_of_cont st block_addr params k kx kf in

  match last with
  | Return x ->
    cps_return x
  | Raise x ->
    let kxret = Var.fresh () in
    [Let (kxret, Apply (kx, [x], true))],
    Return kxret
  | Stop ->
    (* ??? *)
    [], Stop
  | Branch cont ->
    cps_branch' cont
  | Cond (cond, x, cont1, cont2) ->
    [], Cond (cond, x, cps_jump_cont cont1, cps_jump_cont cont2)
  | Switch (x, c1, c2) ->
    [], Switch (x, Array.map cps_jump_cont c1, Array.map cps_jump_cont c2)
  | Pushtrap (cont1, x, cont2, pc) ->
    st.kx_of_poptrap <- AddrMap.add pc kx st.kx_of_poptrap;

    let id_addr = add_block st (identity ()) in
    let id_k, v = fresh2 () in

    Printf.eprintf "=>>>>> handler addr: %d\n" (fst cont2);
    let handler, handler_closure =
      closure_of_cont st block_addr [x] id_k kx kf cont2 in

    Printf.eprintf "<== %d\n" block_addr;
    begin match AddrMap.find block_addr st.en.exit_of_entry with
      | None ->
        [Let (id_k, Closure ([v], (id_addr, [v])));
         Let (handler, handler_closure)] @>
        cps_branch st block_addr id_k handler kf cont1
        
      | Some cont_addr ->
        let cont_block = IntMap.find cont_addr st.blocks in
        let dummy, dummy_v, body_ret = fresh3 () in
        let body, body_closure =
          closure_of_cont st block_addr [dummy] id_k handler kf cont1 in

        let continue_instrs, last =
          if AddrSet.mem cont_addr (AddrMap.find block_addr st.delimited_by) then
            [], Return body_ret
          else begin
            Printf.eprintf "<> find defs of exit node: %d\n" cont_addr;
            let (scope_defs, entry_defs) = AddrMap.find cont_addr st.defs_of_exit_node in
            let l = List.filter (in_this_scope scope_defs) cont_block.params in
            assert (List.length l = 1);
            let interesting_param = List.hd l in
            let interesting_arg = Var.fresh () in
            let args = List.map (fun v ->
              if v = interesting_param then interesting_arg
              else entry_def_of scope_defs entry_defs v) cont_block.params in

            let call_cont_block =
              { params = [interesting_arg];
                handler = None;
                body = [];
                branch = Branch (cont_addr, k :: kx :: kf :: args) } in
            let call_cont_addr = add_block st call_cont_block in
            
            let cont, cont_ret, v' = fresh3 () in
            [Let (cont, Closure ([v'], (call_cont_addr, [v'])));
             Let (cont_ret, Apply (cont, [body_ret], true));],
            Return cont_ret
          end
        in

        [Let (id_k, Closure ([v], (id_addr, [v])));
         Let (handler, handler_closure);
         Let (body, body_closure);

         Let (dummy_v, Const 0l);
         Let (body_ret, Apply (body, [dummy_v], true));
        ] @ continue_instrs,
        last
    end

  | Poptrap cont ->
    let old_kx = AddrMap.find (fst cont) st.kx_of_poptrap in
    cps_branch st block_addr k old_kx kf cont
  | Resume (ret, (stack, func, args), cont_opt) ->
    (if VarSet.mem stack !alloc_stack_vars then
       let ret' = Var.fresh () in
       [Let (ret', Apply (stack, [func; args], true));
        Let (ret, Prim (Extern "caml_trampoline", [Pv ret']))]
     else
       [Let (ret, Apply (stack, [func; args], true))]) @>
    begin match cont_opt with
      | None ->
        cps_return ret
      | Some cont ->
        cps_branch' cont
    end
        
  | Perform (ret, eff, cont) ->
    let cur_stack = Var.fresh () in
    let f, v = fresh2 () in
    let kfret = Var.fresh () in
    let cur_k, cur_k_closure = closure_of_cont' [ret] cont in
    let stack = add_block st (alloc_stack cur_k kx kf) in
    let kf_args = Var.fresh () in
    [Let (cur_k, cur_k_closure);
     Let (cur_stack, Closure ([f; v], (stack, [f; v])));
     Let (kf_args, JSArray [|eff; cur_stack|]);
     Let (kfret, Prim (Extern "caml_trampoline_return", [Pv kf; Pv kf_args]))],
    Return kfret
  | Delegate (eff, stack) ->
    let kfret, kf_args = fresh2 () in
    [Let (kf_args, JSArray [|eff; stack|]);
     Let (kfret, Prim (Extern "caml_trampoline_return", [Pv kf; Pv kf_args]))],
    Return kfret
  | LastApply (ret, (f, args, full), cont_opt) ->
    begin match cont_opt with
      | None ->
        [Let (ret, Apply (f, k :: kx :: kf :: args, full))],
        Return ret
      | Some cont ->
        let cur_k, cur_k_closure = closure_of_cont' [ret] cont in
        let ret' = Var.fresh () in
        [Let (cur_k, cur_k_closure);
         Let (ret', Apply (f, cur_k :: kx :: kf :: args, full))],
        Return ret'
    end

let cps_instr
    st
    (kx: Var.t) (kf: Var.t)
    (instr: instr):
  instr list =
  match instr with
  | Let (x, Prim (Extern "caml_alloc_stack", [Pv hv; Pv hx; Pv hf])) ->
    alloc_stack_vars := VarSet.add x !alloc_stack_vars;
    cps_alloc_stack st x kx kf hv hx hf
  | Let (x, Prim (Extern "caml_bvar_create", [Pv y]))
  | Let (x, Prim (Extern "caml_bvar_take", [Pv y])) ->
    (* TODO *)
    let id, v = fresh2 () in
    let id_addr = add_block st (identity ()) in
    [Let (id, Closure ([v], (id_addr, [v])));
     Let (x, Apply (id, [y], true))]
  | Let (x, Closure (params, (pc, args))) ->
    let k, kx, kf = fresh3 () in
    [Let (x, Closure (k :: kx :: kf :: params, (pc, k :: kx :: kf :: args)))]
  | Let (_, Apply _) ->
    assert false
  | _ ->
    [instr]

let cps_block st block_addr block =
  let k, kx, kf = fresh3 () in
 
  let alloc_jump_closure =
    try
      let to_allocate = IntMap.find block_addr st.jc.closure_of_alloc_site in
      List.map (fun (cname, jump_addr) ->
        let jump_block = IntMap.find jump_addr st.blocks in
        let k, kx, kf = fresh3 () in
        let fresh_params =
          k :: kx :: kf :: List.map (fun _ -> Var.fresh ()) jump_block.params in
        Let (cname, Closure (fresh_params, (jump_addr, fresh_params)))
      ) to_allocate
    with Not_found ->
      []
  in

  let body =
    (List.map (cps_instr st kx kf) block.body
     |> List.flatten)
    @ alloc_jump_closure in
  
  (* order is important, cps_last expects cps_instr to be run before it for the
     body of the block *)
  let last_instrs, last = cps_last st k kx kf block_addr block.branch in

  { params = k :: kx :: kf :: block.params;
    handler = None;
    body = body @ last_instrs;
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
  let dom_by = dominated_by_node g in
  print_graph blocks g;

  Printf.eprintf "\nidom:\n";

  let idom = immediate_dominator_of_node g dom_by in
  IntMap.iter (fun node dom ->
    Printf.eprintf "%d -> %d\n" node dom;
  ) idom;

  Printf.eprintf "\n";
  
  let blocks = AddrMap.map nop_block blocks in
  (start, blocks, free_pc)

let pr_graph ((start, blocks, _) as p) =
  let g = build_graph blocks start in
  print_graph blocks g;
  p

let f ((start, blocks, free_pc): Code.program): Code.program =
  let (jc, en, db, does) :
    jump_closures *
    trywith_exit_nodes *
    AddrSet.t AddrMap.t *
    (Flow.def array * Var.t VarMap.t) AddrMap.t
    =
    Code.fold_closures (start, blocks, free_pc)
      (fun _ _ (start, _) (jc, en, db, does) ->
         Printf.eprintf ">> Start: %d\n\n" start;
         let cfg = build_graph blocks start in
         let dom_by = dominated_by_node cfg in

         Printf.eprintf "dominated_by: \n";
         AddrMap.iter (fun node dom ->
           Printf.eprintf "%d ->" node;
           AddrSet.iter (fun node' ->
             Printf.eprintf " %d" node') dom;
           Printf.eprintf "\n"
         ) dom_by;
         Printf.eprintf "\n";

         print_graph blocks cfg; Printf.eprintf "%!";

         let closure_jc = jump_closures cfg dom_by in
         let closure_en = trywith_exit_nodes blocks cfg dom_by in
         let closure_db = delimited_by blocks cfg closure_en in
         let closure_does = defs_of_exit_scope blocks cfg closure_en in

         Printf.eprintf "\nidom:\n";

         let idom = immediate_dominator_of_node cfg dom_by in
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

         Printf.eprintf "\nExit node of entry node:\n";
         AddrMap.iter (fun entry exit ->
           Printf.eprintf "%d -> " entry;
           (match exit with
            | None -> Printf.eprintf "None"
            | Some n -> Printf.eprintf "%d" n);
           Printf.eprintf "\n"
         ) closure_en.exit_of_entry;

         Printf.eprintf "\nEntry node of exit node:\n";
         AddrMap.iter (fun exit entries ->
           Printf.eprintf "%d ->" exit;
           AddrSet.iter (fun e -> Printf.eprintf " %d" e) entries;
           Printf.eprintf "\n%!";
         ) closure_en.entry_of_exit;

         Printf.eprintf "\nDelimited by:\n";
         AddrMap.iter (fun addr delim ->
           Printf.eprintf "%d ->" addr;
           AddrSet.iter (fun e -> Printf.eprintf " %d" e) delim;
           Printf.eprintf "\n%!";
         ) closure_db;

         Printf.eprintf "\nDefs of exit scope:\n";
         AddrMap.iter (fun exit (defs, entry_defs) ->
           Printf.eprintf "- Exit %d:\n" exit;
           Printf.eprintf "+ defs:\n";
           Array.iteri (fun i d ->
             Printf.eprintf "%d ->" i;
             (match d with
              | Flow.Phi s ->
                VarSet.iter (fun v -> Printf.eprintf " v%d" (Var.idx v)) s
              | Flow.Expr _ -> Printf.eprintf " Expr"
              | Flow.Param -> Printf.eprintf " Param"
              | Flow.FromOtherStack -> Printf.eprintf " FromOtherStack");
             Printf.eprintf "\n"
           ) defs;

           Printf.eprintf "+ Entry defs:\n";
           VarMap.iter (fun k v ->
             Printf.eprintf "v%d -> v%d\n" (Var.idx k) (Var.idx v)
           ) entry_defs;
           Printf.eprintf "\n";
           
         ) closure_does;

         (merge_jump_closures closure_jc jc,
          merge_exit_nodes closure_en en,
          merge_delimited_by closure_db db,
          merge_defs_of_exit_scope closure_does does)
      ) (empty_jump_closures, empty_exit_nodes, AddrMap.empty, AddrMap.empty)
  in

  let st = { new_blocks = AddrMap.empty, free_pc; blocks; jc; en;
             delimited_by = db;
             defs_of_exit_node = does;
             kx_of_poptrap = AddrMap.empty } in
  let blocks = cps_blocks st in

  Printf.eprintf "Cont closures:";
  VarSet.iter (fun c -> Printf.eprintf " v%d" (Var.idx c)) !cont_closures;
  Printf.eprintf "\n\n%!";

  let k, kx, kf = fresh3 () in
  let v1, v2, v3, v4 = fresh4 () in
  let toplevel_k_addr = add_block st (toplevel_k ()) in
  let toplevel_kx_addr = add_block st (toplevel_kx ()) in
  let toplevel_kf_addr = add_block st (toplevel_kf ()) in
  let new_start = add_block st {
    params = [];
    handler = None;
    body = [
      Let (k, Closure ([v1], (toplevel_k_addr, [v1])));
      Let (kx, Closure ([v2], (toplevel_kx_addr, [v2])));
      Let (kf, Closure ([v3; v4], (toplevel_kf_addr, [v3; v4])))
    ];
    branch = Branch (start, [k; kx; kf])
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
