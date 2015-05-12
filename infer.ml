open Batteries
open Type

open Shape

(* NOTE: We need to keep track of subeffecting constraints almost everywhere.
   When we instantiate a variable we get subeffecting constraints, that must
   be propagated bottom-up, until we reach a function definition.
   However, constraints are not necessary to type-check expressions,
   so we don't push them into subterms.
 *)

(* NOTE: Variable declarations cannot be generalized:
		int x = 1
	equals to
		let x = ref 1
	this would not be sound, we also impose the value restriction.
 *)

let instantiate :shape scheme -> shape * K.t =
	fun { vars; body = shp} ->
	let qvs = Vars.to_list vars in
	let mtvs = Var.meta_of_list qvs in
	let s = Subst.mk (List.combine qvs mtvs) in
	let shp' = Shape.vsubst s shp in
	let k = Vars.filter Var.is_effect (fv_of shp') in
	shp', k

(* THINK: move this into type because it knows a lot about the internals *)
(* If we generalize meta-type variables we could just write the meta variables and then zonk, instead of substitution. *)
let quantify (r :Region.t) (vs :Vars.t) (z :shape)
	: shape scheme =
	let ys = Vars.to_list vs in
	let xs = Var.bound_of_list ys in
	(* write into vs's *)
	List.iter2 Var.write ys xs;
	let xs' = Vars.zonk_lb (Vars.of_list xs) in
	let z' = Shape.zonk z in
	{ vars = xs'; body = Shape.Ref(r,z') }

(* generalize effect-free shapes, such as functions *)
let generalize (env :Env.t) (k :K.t) (r: Region.t) (z :shape)
	: shape scheme * K.t =
	let rr = Region.zonk r in
	let zz = Shape.zonk z in
	let z_fv = Shape.fv_of zz in
	let env_fv = Env.fv_of (Env.zonk env) in
	let vs = Vars.diff z_fv env_fv in
	let k1 = K.minus k vs in
	let sch = quantify rr vs zz in
	sch, k1

let rec principal_effects f =
	Enum.concat (Enum.map principal_effects_e (Effects.enum f))

and principal_effects_e (f :Effects.e) :Effects.e Enum.t =
	match f with
	| Effects.Var x ->
		let en = principal_effects (EffectVar.lb_of x) in
		Enum.push en f;
		en
	| _____________ -> Enum.singleton f

let observe (env :Env.t) :E.t -> E.t =
	let env_fv = Env.fv_of (Env.zonk env) in
    let is_observable = function
		| E.Var x     -> Vars.mem (Var.Effect x) env_fv
		| E.Mem(_k,r) -> Vars.mem (Var.Region r) env_fv
	in
	E.of_enum % Enum.filter is_observable % principal_effects % E.zonk

(* TODO: We should keep "precision" info associated with
   region variables. E.g. to know if something is the result
   of unsafe pointer arithmetic.
 *)

let of_const : Cil.constant -> shape
	= function
	| Cil.CInt64 _ -> Shape.fresh()
	| Cil.CStr _   -> Bot
	| Cil.CWStr _  -> Bot
	| Cil.CChr _   -> Bot
	| Cil.CReal _  -> Bot
	| Cil.CEnum _  -> Bot

let of_unop (_env :Env.t) z
		: Cil.unop -> shape * Effects.t
	= function
	| Cil.LNot   -> Shape.Bot, Effects.none
	| __other__  -> z, Effects.none

(* For now, we just pick the shape of the first argument, which in CIL,
   it's always the pointer argument. This may be unsound in some corner
   (rare?) cases, but we are unsound anyways. Better to be precise in the
   majority of cases.

   TODO: PlusPI -> mark that a pointer is the result of arithmetic
		 MinusPP -> warn if after unification the two regions are different
 *)
let of_binop (_env :Env.t) z1 _z2
		: Cil.binop -> shape * Effects.t
	= function
	| Cil.Eq
	| Cil.Ne
	| Cil.Lt
	| Cil.Le
	| Cil.Gt
	| Cil.Ge
	| Cil.LAnd
	| Cil.LOr
		-> Shape.Bot, Effects.none
	| __other__ -> z1, Effects.none

let rec of_exp (env :Env.t)
	: Cil.exp -> shape * Effects.t * K.t
	= function
	| Cil.Const c
	-> of_const c, Effects.none, K.none
	| Cil.Lval lv
	-> let z, f, k = of_lval env lv in
	   let r, z0 = Unify.match_ref_shape z in
	   let f' = E.(f + read r) in
	   z0, f', k
	(* Even though effectively [unsigned int] or the like,
	 * it seems a terrible idea to cast [size_t] to a
	 * pointer type, so we give it shape _|_.
	 *)
	| Cil.SizeOf _
	| Cil.SizeOfE _
	| Cil.SizeOfStr _
	| Cil.AlignOf _
	| Cil.AlignOfE _
	-> Bot, Effects.none, K.none
	(* These operators may add effect, but they don't hide
	   any of the effects of their arguments *)
	| Cil.UnOp (op,e,_ty)
	-> let z, f, k = of_exp env e in
	   let z1, f1 = of_unop env z op in
	   z1, Effects.(f + f1), k
	| Cil.BinOp (op,e1,e2,ty)
	-> let z1, f1, k1 = of_exp env e1 in
	   let z2, f2, k2 = of_exp env e2 in
	   let z3, f3 = of_binop env z1 z2 op in
	   z3, Effects.(f1 + f2 + f3), K.(k1 + k2)
	| Cil.Question (e1,e2,e3,ty) ->
	  let _z1, f1, k1 = of_exp env e1 in
	  let  z2, f2, k2 = of_exp env e2 in
	  let  z3, f3, k3 = of_exp env e3 in
	  Unify.(z2 =~ z3);
	  z2, Effects.(f1 + f2 + f3), K.(k1 + k2 + k3)
	| Cil.CastE (ty,e)
	-> let z, f, k = of_exp env e in
	   let z1 = Unify.match_shape_with_typ z ty in
	   z1, f, k
	| Cil.AddrOf lv
	-> let z, f, k = of_lval env lv in
	   Ptr z, f, k
	(* TODO: This is a GCC extension, I hope not a popular one :-) *)
	| Cil.AddrOfLabel _  -> Error.not_implemented()
	(* startof is a CIL operator to represent the implicit cast
	   between an array variable to a pointer to the first element,
	   effectively [id] for us.
	 *)
	| Cil.StartOf lv
	-> of_lval env lv

and of_lval (env :Env.t)
	: Cil.lval -> shape * Effects.t * K.t
	= function (lhost,offset) ->
		let z, f, k = of_lhost env lhost in
		let z1, f1, k1 = with_offset env z offset in
		z1, Effects.(f + f1), K.(k + k1)

and with_offset (env: Env.t) (z :shape)
	: Cil.offset -> shape * Effects.t * K.t
	= function
	| Cil.NoOffset      -> z, Effects.none, K.none
	(* array indexing *)
	| Cil.Index (e,off) ->
		let _z0, f0, k0 = of_exp env e in
		(* z = ref z1 *)
		let r, z1 = Unify.match_ref_shape z in
		(* z = ref ptr z2 *)
		let z2 = Unify.match_ptr_shape z1 in
		z2, Effects.(f0 + read r), k0
	(* record field *)
	| Cil.Field _ -> Error.not_implemented()

and of_lhost (env :Env.t)
	: Cil.lhost -> shape * Effects.t * K.t
	= function
	| Cil.Var x ->
		let sch = Env.find x env in
		let z, k = instantiate sch in
		(* assert (is_ref_shape z) ? *)
		z, Effects.none, k
	| Cil.Mem e ->
		let z, f, k = of_exp env e in
		let z1 = Unify.match_ptr_shape z in
		z1, f, k

let with_lval_set (env :Env.t) z f k lv : Effects.t * K.t =
	let z1, f1, k1 = of_lval env lv in
	let r, z0 = Unify.match_ref_shape z1 in
	Unify.(z0 =~ z);
	Effects.(f + f1 + write r), K.(k + k1)

let of_instr (env :Env.t)
	: Cil.instr -> Effects.t * K.t
	= function
	| Cil.Set (lv,e,_loc)
	-> let z, f, k = of_exp env e in
	   with_lval_set env z f k lv
	| Cil.Call (lv_opt,fn,es,_loc)
	-> (* z' fn(zs) | f *)
	   let z0, f0, k0 = of_exp env fn in
	   let zs, f, z' = Shape.get_fun z0 in
	   (* evaluation: sum of effects and constraints *)
	   let sf, sk = List.fold_left2
		(fun (f,k) z e ->
			let ez, ef, ek = of_exp env e in
			let _r, z1 = Unify.match_ref_shape z in
			Unify.(z1 =~ ez);
			Effects.(ef + f), K.(ek + k)
		)
		E.(just_var f + f0,k0) zs es in
	   begin match lv_opt with
	   | None    -> sf, sk
	   | Some lv -> with_lval_set env z' sf sk lv
	   end
	(* Oops, unsound :_( *)
	| Cil.Asm _ ->
		Effects.none, K.none

let sum_f_k : (Effects.t * K.t) list -> Effects.t * K.t
	= List.fold_left
		(fun (f, k) (f1, k1) -> Effects.(f1 + f), K.(k1 + k))
		(Effects.none, K.none)

(* TODO: CIL Cfg builds a control-flow graph on the AST structure,
   each stmt receives an id, that we can use to map stmt to
   [Effects.t list]. Note that an statement may be a sequence of
   instructions.
 *)

let rec of_stmtkind (env :Env.t) (rz :shape)
	: Cil.stmtkind -> Effects.t * K.t
	= function
	| Cil.Instr is
	-> sum_f_k (List.map (of_instr env) is)
	| Cil.Return (e_opt,_loc)
	-> begin match e_opt with
	   | None   ->
		   Effects.none, K.none
	   | Some e
	   -> let z, f, k = of_exp env e in
	      Unify.(z =~ rz);
	      f, k
	   end
	(* this is just control-flow, no effects *)
	| Cil.Goto _
	| Cil.Break _
	| Cil.Continue _
	-> Effects.none, K.none
	(* TODO: still unsupported GCC extension *)
	| Cil.ComputedGoto _
	-> Error.not_implemented()
	| Cil.If (e,b1,b2,_loc)
	-> let _z0, f0, k0 = of_exp env e in
	   let      f1, k1 = of_block env rz b1 in
	   let      f2, k2 = of_block env rz b2 in
	   Effects.(f0 + f1 + f2), K.(k0 + k1 + k2)
	| Cil.Switch _
	-> Error.not_implemented()
	(* The last two elements in the tuple refer to CFG instrumentation. *)
	| Cil.Loop (b,_loc,_continue,_break)
	-> of_block env rz b
	| Cil.Block b
	-> of_block env rz b
	(* Not interested in supporting these two from MSVC *)
	| Cil.TryFinally _
	| Cil.TryExcept _
	-> Error.not_implemented()

and of_stmt (env :Env.t) (rz :shape) (s :Cil.stmt) : E.t * K.t =
	of_stmtkind env rz Cil.(s.skind)

and of_block (env :Env.t) (rz :shape) (b :Cil.block) : E.t * K.t =
	 sum_f_k (List.map (of_stmt env rz) Cil.(b.bstmts))

(** Inference rule for function definitions
  *
  * NB: env must include the function itself (we assume it can be recursive).
  *)
let of_fundec (env :Env.t) (k :K.t) (fd :Cil.fundec)
		: shape scheme * K.t =
	let fn = Cil.(fd.svar) in
	let shp' = (Env.find fn env).body in (* TODO: should it be instantiate? *)
	let f_r, shp'' = Unify.match_ref_shape shp' in
	let z_args,f,z_res  = Shape.get_fun shp'' in
	let args_bs = List.map2 (fun x y -> x, Scheme.of_shape y)
		Cil.(fd.sformals)
		z_args
	in
	let env' = Env.with_bindings args_bs env in
	let env'' = Env.with_fresh_bindings Cil.(fd.slocals) env' in
	let body = Cil.(fd.sbody) in
	(* THINK: Maybe we don't need to track constraints but just compute them
	   as the FV of the set of effects computed for the body of the function? *)
	let bf, k1 = of_block env'' z_res body in
	let bf' = observe env' bf in (* FIXME in the paper: not env but env'! *)
	(* f >= bf' may introduce a recursive subeffecting constraint
	   if the function is recursive.
	   Possible FIX? Create a new fresh effect variable? f' >= bf'?
	   Possible FIX? Remove f from bf'?
	   What about mutually recursive functions?
	 *)
	let k2 = K.add f bf' k1 in
	(* THINK: Maybe we should generalize in of_global *)
	generalize (Env.remove fn env) k2 f_r shp''

let of_global (env :Env.t) (k :K.t) : Cil.global -> Env.t * K.t = function
	(* THINK: Do we need to do anything here? CIL has this unrollType helper
	   that should be enough...
	 *)
	| Cil.GType _ -> Error.not_implemented()
	| Cil.GCompTag _
	| Cil.GCompTagDecl _ -> Error.not_implemented()
	| Cil.GEnumTag _
	| Cil.GEnumTagDecl _ -> Error.not_implemented()
	| Cil.GVarDecl (x,_) ->
		let xn = Cil.(x.vname) in
		(* Errormsg.log "Variable declaration: %s : %a\n" xn Cil.d_type Cil.(x.vtype); *)
		if Hashtbl.mem Cil.builtinFunctions xn
		then (Log.info "Skipping builtin function: %s\n" xn;
			  env, k)
		else Env.fresh_if_absent x env, k
	| Cil.GVar (x,ii,_) ->
		let xn = Cil.(x.vname) in
		let env' = Env.fresh_if_absent x env in
		Log.info "Global variable %s : %s\n" xn (Shape.to_string (Env.find x env').body);
		(* THINK: move to of_init *)
		let k' = Cil.(ii.init) |> Option.map_default (function
			| Cil.SingleInit e ->
				let ze, fe, ke = of_exp env e in
				let _f1, k1 = with_lval_set env' ze fe ke (Cil.var x) in
				K.(k + k1)
			| Cil.CompoundInit _ -> Error.not_implemented()
		) k
		in
		env', k'
	| Cil.GFun (fd,_) ->
		let fn = Cil.(fd.svar) in
		Log.debug "In function %s\n" Cil.(fn.vname);
		(* we may know about fn already, if there is any function declaration *)
		let env' = Env.fresh_if_absent fn env in
		(* infer *)
		let sch, k1 = of_fundec env' k fd in
		Log.info "Function %s : %s\n" Cil.(fn.vname) (Shape.to_string sch.body);
		(* new environment with f generalized,
		 * this overwrites any previous binding.
		 *)
		Env.add fn sch env, k1
	(* Oooh, we're unsound here :_( *)
	| Cil.GAsm _
	| Cil.GPragma _ -> env, k
	(* Nothing to be done *)
	| Cil.GText _ -> env, k

(* TODO: globinit ? *)
let of_file (file : Cil.file) :unit =
	(* TODO: Here we can read axioms *)
	let env0 = Env.empty in
	let k0 = K.none in
	let env1, _ = List.fold_left
		(fun (env,k) gbl ->	of_global env k gbl)
		(env0,k0)
		Cil.(file.globals)
	in
	Log.info "Env:\n %s\n" (Env.to_string (Env.zonk env1));
	()
