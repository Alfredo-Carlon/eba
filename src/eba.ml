
open Batteries
open Cmdliner

open Abs

module L = LazyList

type checks = {
	  chk_uninit : bool
	; chk_dlock  : bool
	; chk_uaf    : bool
	; chk_birq   : bool
}

let run_checks checks file fileAbs :unit =
	let run_check_fun fd in_func =
		let with_warn_out print =
			if Opts.Get.warn_output()
			then File.with_file_out (Cil.(file.fileName) ^ ".warn") print
			else print IO.stdout
		in
		in_func fileAbs fd |> L.iter (fun errmsg ->
		 	with_warn_out (fun out ->
				Printf.fprintf out "\nPotential BUG found:\n%s\n\n" errmsg
			)
		)
	in
	let fds = Cil.(file.globals) |> List.filter_map (function
		| Cil.GFun(fd,_) -> Some fd
		| ______________ -> None
	)
	in
	(* THINK: Too much if-ery? *)
	fds |> List.iter (fun fd ->
		Log.debug "Analyzing function %s\n" Cil.(fd.svar.vname);
		if checks.chk_uninit
		then run_check_fun fd CheckUninitFlow1.in_func;
		if checks.chk_uaf
		then run_check_fun fd CheckUAF.in_func;
		if checks.chk_dlock
		then run_check_fun fd CheckDLockFlow2.in_func;
		if checks.chk_birq
		then run_check_fun fd CheckBhOnIrqFlow2.in_func;
	)

                  (******** EBA-CIL CFG **********)

(******* CFG generator to include regions and shapes per instruction *******)
(* Basic cfg node, it includes the id of the basic block and a forward and backward adjacency list *)
type eba_cfg_node =
  {
    id : int list;
    predc : int list;
    succ : int list;
  }
(*A CIL statement and its labeling in shapes & effects & regions *)
type eba_cfg_stmtreg =
  {s : Cil.stmt list; (* The statement *)
   regs : Cil.stmt list; (*The s&e&r*)
  }

(* The data inside each basic block *)
type eba_cfg_data =
  {ident : int;
   stmts : Cil.stmt * Cil.stmt; (*Instructions inside the basic block*)
  }

type eba_cfg =
  {
    (* The CFG as an adjacency list *)
    cfg : eba_cfg_node list;
    (* The data of each node in the CFG *)
    data : eba_cfg_data list;
  }

let create_cfg (fd:Cil.fundec) eba_fd =
  let basic_cfg = List.map (fun (stmt:Cil.stmt) ->
                      let sid_proj (x:Cil.stmt) = x.sid in
                      {id = stmt.sid::[]; predc = List.map sid_proj stmt.preds; succ = List.map sid_proj stmt.succs}) fd.sallstmts in

  let eq_ x y = x=y in
  let rec find_node n_id ccfg  = match ccfg with
          | hd::xs -> begin
              if List.exists (eq_ n_id) hd.id then hd else find_node n_id xs
            end
          | [] -> assert false (*Should not happen *) in
  (* Merge the cfg nodes *)
  let rec merge_cfg (cfg:eba_cfg_node list) =
    let branch_nodes = List.map (fun n -> List.hd n.id) (List.filter (fun (node:eba_cfg_node ) -> (List.length node.succ) > 1) cfg) in
    (**** Mergable nodes fulfill:
          1. They have only one predecessor.
          2. They have only one successor.
          3. The predecessor is not a branch node *****)
    (**** Fix point merging ****)
    try let mergable = List.find (fun (node:eba_cfg_node) -> (List.length node.predc) = 1 &&
                                                               (List.length node.succ) = 1 &&
                                                                 not (List.exists (eq_ (List.hd node.predc)) branch_nodes))cfg in
        let pred_node = find_node (List.hd mergable.predc) cfg in
        let new_node = {id = List.append pred_node.id mergable.id; predc = pred_node.predc; succ = ((List.hd mergable.succ) ::
                                                                                              (List.filter (fun n -> not (n = List.hd mergable.id)) pred_node.succ))} in
        let new_cfg = new_node :: (List.filter (fun (node:eba_cfg_node) -> not (List.exists (fun n -> (n = List.hd mergable.id) || (n = List.hd pred_node.id))node.id)) cfg) in
        merge_cfg new_cfg
    with Not_found -> cfg in
  (* Collapse long names *)
  let collapse_names (cfg:eba_cfg_node list) =
    (* Main re-label of CFG nodes but keep the original tag list so we can then add the relevant instructions from CIL nodes *)
    let dictionary = List.mapi (fun i (tags,_) -> (tags,i))
                       (List.sort (fun (_,id1) (_,id2) -> if id1 < id2 then -1 else if id1 > id2 then 1 else 0)
                          (List.map (fun (node:eba_cfg_node) -> (node.id, List.hd node.id)) cfg)) in
    (* Lookup final tag, aux function *)
    let rec find_tag dictionary id = match dictionary with
      | (merged, label)::xs -> if List.exists (fun merged_id -> merged_id = id) merged then label else find_tag xs id
      | [] -> assert false (*Should not happen*) in
    (* Actual re-labeling *)
    (dictionary, List.map (fun (node:eba_cfg_node) -> {id = [find_tag dictionary (List.hd node.id)]; predc = List.map (find_tag dictionary) node.predc;
                                          succ = List.map (find_tag dictionary) node.succ;}) cfg )in
  let rec fill_cil dictionary = match dictionary with
    |(tags, i)::xs -> (i,List.map (fun nid -> List.find (fun (stmt:Cil.stmt) -> stmt.sid = nid) fd.sallstmts) tags)::fill_cil xs
    |[] -> [] in

  (*let rec fill_eba = List.map (fun stmt -> AFun.shape_of eba_fd stmt) fd.slocals  in*)
    
  let (dictionary, graph) = collapse_names (merge_cfg basic_cfg) in
  let (g,d) = (graph, fill_cil dictionary) in
  (* Testing to find out EBA's structure *)
  (g,d,AFile.find_fun eba_fd fd.svar)
  
  
let rec nodes_dot_code (rootn : eba_cfg_node list) =
  match rootn with
  |hd::xs -> (List.fold_left (fun prev n -> prev ^ string_of_int (List.hd hd.id) ^ "->" ^ (string_of_int n) ^ "\n") "" hd.succ) ^ (nodes_dot_code xs)
  |[] -> ""


(* String of statements, returns a string for every statemet in the stmts list *)
let rec string_of_stmts stmts eba_fun =
  (*String representation of an expression *)
  let rec string_of_exp (exp:Cil.exp) = match exp with
    | Const _ -> "Constant"
    | Lval a -> string_of_set a 
    | AddrOf adr -> (string_of_set adr)
    | _ -> "unknown" 
  (*String representation of a variable/pointer set (lval) *)
  and string_of_set (set:Cil.lval) =
    match set with
    | (Mem m, _) -> "Pointer: " ^ string_of_exp m
    | (Var a, _) -> try a.vname ^ Type.Regions.to_string (AFun.regions_of eba_fun a)
                    with Not_found -> a.vname
    (*| (Var a, _) -> match (a.vtype:Cil.typ) with
                    |Cil.TFun(_,_,_,_) -> a.vname
                    |_ -> a.vname ^ Type.Regions.to_string (AFun.regions_of eba_fun a)*)
  in
  (* String of an instruction *)
  let string_of_inst (inst:Cil.instr) = match inst with
    | Set (l,e,loc) -> "Set: " ^ string_of_set l
    | Call (l, e, args,loc) -> "Call: " ^ string_of_exp e
    | Asm _ -> "ASM" in
(* String of an statement, returns a string representation of stmt based on its type *)
  let string_of_stmt (stmt:Cil.stmt) = match stmt.skind with
    | If (e, _, _, _)  -> "if" (*sprint ~width:999 (dprintf "if %a" d_exp e)*)
    | Loop _ -> "loop"
    | Break _ -> "break"
    | Continue _ -> "continue"
    | Goto _ | ComputedGoto _ -> "goto"
    | Instr i -> List.fold_left (^) "" (List.map (fun i -> "\t"^ string_of_inst i ^ "\n") i )
    | Switch _ -> "switch"
    | Block _ -> "block"
    | Return _ -> "return"
    | TryExcept _ -> "try-except"
    | TryFinally _ -> "try-finally" in

  match stmts with
  |(i,stmts)::sx -> string_of_int i ^ " -> " ^ List.fold_left (fun prev stmt -> prev ^ (string_of_stmt stmt) ^ "\n") "" stmts ^ string_of_stmts sx eba_fun
  | [] -> ""
  
  
(******* Entry point ******)        
(* Dumps .dot files for every function declared in the file
 Note: is file mutated in infer_file?*)
(* Should be Cil.file -> unit *)
let dump_cfg cil_file gcc_filename eba_file =
  (*Dumps dot format basic code for all nodes from the root node*)
  Cil.iterGlobals cil_file (fun g ->
      (*************************** 'when' added just for testing purposes ***************)
      match g with GFun(fd, _) (*when fd.svar.vname = "get_domain_for_dev"*) ->
                    (*Dump .dot file *)
                 (*Cfg.printCfgFilename (gcc_filename ^"."^(fd.svar.vname)^".dot") fd*)
                 (* Printf.printf "%s\n" fd.svar.vname; create_cfg fd;()*)
                    let filename = gcc_filename ^ "."^(fd.svar.vname)^".dot" in
                    let chan = open_out filename in
                    let (rootn, stmts,Some(_,ebaFun))  = create_cfg fd eba_file in
                    Printf.printf "digraph CFG_%s {\n %s}\n" fd.svar.vname (nodes_dot_code rootn);
                    Printf.printf "%s" (string_of_stmts stmts ebaFun)
                 | _ -> ())

                                                (******** End: EBA-CIL CFG **********)

let infer_file checks fn =
	let file = Frontc.parse fn () in
	let fileAbs = Infer.of_file file in
	if Opts.Get.save_abs()
	then begin
		let fn_abs = fn ^ ".abs" in
		File.with_file_out fn_abs (fun out -> AFile.fprint out fileAbs)
                dump_cfg file fn fileAbs
	end;
	run_checks checks file fileAbs;
	if Opts.Get.gc_stats()
	then begin
		Printf.fprintf stderr "======= GC stats =======\n";
		Gc.print_stat stderr;
		Printf.fprintf stderr "========================\n"
	end

let infer_file_gcc checks args =
	let fn = Gcc.gcc args in
	infer_file checks fn

(* CLI *)

let log_level_of_int = function
	| x when x <= 0 -> Log.ERROR
	| 1 -> Log.WARN
	| 2 -> Log.INFO
	| x -> Log.DEBUG (* x >= 3 *)

let infer_files verbosity
		flag_gcstats flag_saveabs flag_warn_output flag_fake_gcc
		flag_no_dce flag_no_dfe flag_safe_casts flag_externs_do_nothing
		opt_inline_limit opt_loop_limit opt_branch_limit flag_no_path_check
		flag_all_lock_types flag_no_match_lock_exp flag_ignore_writes
		chk_uninit chk_dlock chk_uaf chk_birq
		files =
	(* CIL: do not print #line directives. *)
	Cil.lineDirectiveStyle := None;
	Log.color_on();
	Log.set_log_level (log_level_of_int verbosity);
	Opts.Set.gc_stats flag_gcstats;
	Opts.Set.save_abs flag_saveabs;
	Opts.Set.warn_output flag_warn_output;
	Opts.Set.dce (not flag_no_dce);
	Opts.Set.dfe (not flag_no_dfe);
	Opts.Set.unsafe_casts (not flag_safe_casts);
	Opts.Set.externs_do_nothing flag_externs_do_nothing;
	Opts.Set.inline_limit opt_inline_limit;
	Opts.Set.loop_limit opt_loop_limit;
	Opts.Set.branch_limit opt_branch_limit;
	Opts.Set.path_check (not flag_no_path_check);
	Opts.Set.all_lock_types flag_all_lock_types;
	Opts.Set.match_lock_exp (not flag_no_match_lock_exp);
	Opts.Set.ignore_writes flag_ignore_writes;
	let checks = { chk_uninit; chk_dlock; chk_uaf; chk_birq } in
	Axioms.load_axioms();
	if flag_fake_gcc
	then infer_file_gcc checks files
	else begin
		List.iter Utils.check_if_file_exists files;
		List.iter (infer_file checks) files
	end

let files = Arg.(non_empty & pos_all string [] & info [] ~docv:"FILE")

(* General *)

(* TODO: Write a Cmdliner.converter for Log.log_level *)
let verbose =
	let doc = "Set the verbosity level." in
	Arg.(value & opt int 0 & info ["v"; "verbose"] ~docv:"LEVEL" ~doc)

let flag_gcstats =
	let doc = "Print GC stats after analyzing a C file." in
	Arg.(value & flag & info ["gc-stats"] ~doc)

let flag_saveabs =
	let doc = "Save effect abstraction to an .abs file." in
	Arg.(value & flag & info ["save-abs"] ~doc)

let flag_warn_output =
	let doc = "Save warns into a .warn file." in
	Arg.(value & flag & info ["warn-output"] ~doc)

let flag_fake_gcc =
	let doc = "Fake GCC and preprocess input file." in
	Arg.(value & flag & info ["fake-gcc"] ~doc)

(* Type inferrer*)

let flag_no_dce =
	let doc = "Do not eliminate dead code." in
	Arg.(value & flag & info ["no-dce"] ~doc)

let flag_no_dfe =
	let doc = "Do not ignore unused fields in structure types (aka dead field elimination)." in
	Arg.(value & flag & info ["no-dfe"] ~doc)

let flag_safe_casts =
	let doc = "Fail on potentially unsafe casts." in
	Arg.(value & flag & info ["safe-casts"] ~doc)

let flag_externs_do_nothing =
	let doc = "Ignore potential side-effects of extern functions." in
	Arg.(value & flag & info ["externs-do-nothing"] ~doc)

(* Model checker *)

let opt_inline_limit =
	let doc = "Inline function calls up to $(docv) times. Provide -1 to prevent inlining but accept some false positives." in
	let def = Opts.Get.inline_limit() in
	Arg.(value & opt int def & info ["inline-limit"] ~docv:"N" ~doc)

let opt_loop_limit =
  let doc = "Take up to $(docv) loop iterations." in
  let def = Opts.Get.loop_limit() in
  Arg.(value & opt int def & info ["loop-limit"] ~docv:"N" ~doc)

let opt_branch_limit =
  let doc = "Take up to $(docv) branch decisions." in
  let def = Opts.Get.branch_limit() in
  Arg.(value & opt int def & info ["branch-limit"] ~docv:"N" ~doc)

let flag_no_path_check =
	let doc = "Do not check path consistency." in
	Arg.(value & flag & info ["no-path-check"] ~doc)

(* Double-Lock bug cheker *)

let flag_all_lock_types =
	let doc = "[Double-Lock] Check all lock types (not only spin locks)." in
	Arg.(value & flag & info ["all-lock-types"] ~doc)

let flag_no_match_lock_exp =
	let doc = "[Double-Lock] Do not use heuristics to match lock object expressions." in
	Arg.(value & flag & info ["no-match-lock-exp"] ~doc)

let flag_ignore_writes =
	let doc = "[Double-Lock] Ignore writes that may affect the lock object." in
	Arg.(value & flag & info ["ignore-writes"] ~doc)

(* Bug chekers *)

let check_uninit =
	let doc = "Check for uses of variables before initialization" in
	Arg.(value & flag & info ["U"; "uninit"] ~doc)

let check_dlock =
	let doc = "Check for double locking" in
	Arg.(value & flag & info ["L"; "dlock"] ~doc)

let check_uaf =
	let doc = "Check for use-after-free" in
	Arg.(value & flag & info ["F"; "uaf"] ~doc)

let check_birq =
	let doc = "Check for BH-enabling while IRQs are off" in
	Arg.(value & flag & info ["B"; "bh-irq"] ~doc)

let cmd =
	let doc = "Effect-based analysis of C programs" in
	let man =
	[
		`S "DESCRIPTION";
		`P "Author: Iago Abal <mail@iagoabal.eu>.";

		`P "To preprocess the input use `--fake-gcc' and pass the necessary arguments after `--', as in:";
		`P "eba --fake-gcc -- -Iinclude/ foo.c";
		`P "EBA will extract the `-D', `-include', and `-I' arguments and invoke GCC, any other option will be ignored."
	] in
	Term.(pure infer_files
		$ verbose
		$ flag_gcstats $ flag_saveabs $ flag_warn_output $ flag_fake_gcc
		$ flag_no_dce $ flag_no_dfe $ flag_safe_casts $ flag_externs_do_nothing
		$ opt_inline_limit $ opt_loop_limit $ opt_branch_limit $ flag_no_path_check
		$ flag_all_lock_types $ flag_no_match_lock_exp $ flag_ignore_writes
		$ check_uninit $ check_dlock $ check_uaf $ check_birq
		$ files),
	Term.info "eba" ~version:"0.1" ~doc ~man

let () = match Term.eval cmd with `Error _ -> exit 1 | _ -> exit 0
