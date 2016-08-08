
type copts = {
	(* General *)
	mutable gc_stats : bool;
	mutable save_abs : bool;
	(* Type inferrer *)
	mutable dce : bool;
	mutable dfe : bool;
	mutable unsafe_casts : bool;
	mutable externs_do_nothing : bool;
	(* Model checker *)
	mutable inline_limit : int;
	mutable loop_limit : int;
	mutable branch_limit : int;
	mutable path_check : bool;
}

let opts : copts = {
	gc_stats = false;
	save_abs = false;

	dce = true;
	dfe = true;
	unsafe_casts = true;
	externs_do_nothing = false;

	inline_limit = 5;
	loop_limit = 1;
	branch_limit = 15;
	path_check = true;
}

module Set =
struct

	let gc_stats v = opts.gc_stats <- v

	let save_abs v = opts.save_abs <- v

	let dce v = opts.dce <- v

	let dfe v = opts.dfe <- v

	let unsafe_casts v = opts.unsafe_casts <- v

	let externs_do_nothing v = opts.externs_do_nothing <- v

	let inline_limit v = opts.inline_limit <- v

	let loop_limit v = opts.loop_limit <- v

	let branch_limit v = opts.branch_limit <- v

	let path_check v = opts.path_check <- v

end

module Get =
struct

	let gc_stats () = opts.gc_stats

	let save_abs () = opts.save_abs

	let dce () = opts.dce

	let dfe () = opts.dfe

	let unsafe_casts () = opts.unsafe_casts

	let externs_do_nothing () = opts.externs_do_nothing

	let inline_limit () = opts.inline_limit

	let loop_limit () = opts.loop_limit

	let branch_limit () = opts.branch_limit

	let path_check () = opts.path_check

end
