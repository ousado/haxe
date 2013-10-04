open Ast
open Common
open Type

(*
	Naming conventions:
		e = Type.texpr
		t = Type.t
		p = Ast.pos
		c = Type.tclass
		cf = Type.tclass_field
		*l = ... list
		*o = ... option

	Function names:
		generate_ -> outputs content to buffer
		s_ -> return string

*)

type dependency_type =
	| DFull
	| DForward
	| DCStd

type function_context = {
	field : tclass_field;
	mutable loop_stack : string option list;
	mutable meta : metadata;
}

type hxc = {
	t_typeref : t -> t;
	t_pointer : t -> t;
	t_const_pointer : t -> t;
	t_func_pointer : t -> t;
	t_closure : t -> t;
	t_int64 : t -> t;
	t_jmp_buf : t;
	t_vararg : t;

	c_lib : tclass;
	c_boot : tclass;
	c_string : tclass;
	c_array : tclass;
	c_fixed_array : tclass;
	c_exception : tclass;
	c_cstring : tclass;
	c_csetjmp : tclass;
	c_cstdlib : tclass;
	c_cstdio : tclass;
	c_vtable : tclass;

	cf_deref : tclass_field;
	cf_addressof : tclass_field;
	cf_sizeof : tclass_field;
}

type context = {
	com : Common.context;
	hxc : hxc;
	mutable num_temp_funcs : int;
	mutable num_labels : int;
	mutable num_identified_types : int;
	mutable get_anon_signature : (string,tclass_field) PMap.t -> string;
	mutable type_ids : (string,int) PMap.t;
	mutable type_parameters : (path, texpr) PMap.t;
	mutable init_modules : path list;
	mutable generated_types : type_context list;
	mutable filters : filter list;
}

and type_context = {
	con : context;
	file_path_no_ext : string;
	buf_c : Buffer.t;
	buf_h : Buffer.t;
	type_path : path;
	mutable buf : Buffer.t;
	mutable tabs : string;
	mutable fctx : function_context;
	mutable dependencies : (path,dependency_type) PMap.t;
}

and gen_context = {
	gcom : Common.context;
	gcon : context;
	mutable gfield : tclass_field;
	mutable mtype : module_type option;
	(* call this function instead of Type.map_expr () *)
	mutable map : texpr -> texpr;
	(* tvar_decl -> unit; declares a variable on the current block *)
	mutable declare_var : (tvar * texpr option) -> unit;
	mutable declare_temp : t -> texpr option -> tvar;
	(* runs a filter on the specified class field *)
	mutable run_filter : tclass_field -> unit;
	(* adds a field to the specified class *)
	mutable add_field : tclass -> tclass_field -> bool -> unit;
	(* delays to run after all filters are done *)
	mutable delays : (unit -> unit) list;
}

and filter = gen_context->(texpr->texpr)

let rec follow t =
	match t with
	| TMono r ->
		(match !r with
		| Some t -> follow t
		| _ -> t)
	| TLazy f ->
		follow (!f())
	| TType (t,tl) ->
		follow (apply_params t.t_types tl t.t_type)
	| TAbstract(a,pl) when not (Meta.has Meta.CoreType a.a_meta) ->
		follow (Codegen.Abstract.get_underlying_type a pl)
	| _ -> t

module Analyzer = struct
	let assigns_to_trace = ref false

	let rec run e =
		match e.eexpr with
		| TBinop(OpAssign, {eexpr = TField(_,FStatic({cl_path=["haxe"],"Log"}, {cf_name = "trace"}))}, _) ->
			assigns_to_trace := true
		| _ ->
			Type.iter run e
end


(* Helper *)

let path_to_name (pack,name) = match pack with [] -> name | _ -> String.concat "_" pack ^ "_" ^ name

let get_type_id con t =
	let id = Type.s_type (print_context()) (follow t) in
	try
		PMap.find id con.type_ids
	with Not_found ->
		con.num_identified_types <- con.num_identified_types + 1;
		con.type_ids <- PMap.add id con.num_identified_types con.type_ids;
		con.num_identified_types

let sort_anon_fields fields =
	List.sort (fun cf1 cf2 ->
		match Meta.has Meta.Optional cf1.cf_meta, Meta.has Meta.Optional cf2.cf_meta with
		| false,false | true,true -> compare cf1.cf_name cf2.cf_name
		| true, false -> 1
		| false, true -> -1
	) fields

let pmap_to_list pm = PMap.fold (fun v acc -> v :: acc) pm []

let alloc_temp_func con =
	let id = con.num_temp_funcs in
	con.num_temp_funcs <- con.num_temp_funcs + 1;
	let name = "_hx_func_" ^ (string_of_int id) in
	name, id

module Expr = struct

	let t_path t = match follow t with
		| TInst(c,_) -> c.cl_path
		| TEnum(e,_) -> e.e_path
		| TAbstract(a,_) -> a.a_path
		| _ -> [],"Dynamic"
	
	let mk_runtime_prefix n = "_hx_" ^ n
		
	let mk_static_field c cf p =
		let ta = TAnon { a_fields = c.cl_statics; a_status = ref (Statics c) } in
		let ethis = mk (TTypeExpr (TClassDecl c)) ta p in
		let t = monomorphs cf.cf_params cf.cf_type in
		mk (TField (ethis,(FStatic (c,cf)))) t p

	let mk_static_call c cf el p =
		let ef = mk_static_field c cf p in
		let tr = match follow ef.etype with
			| TFun(args,tr) -> tr
			| _ -> assert false
		in
		mk (TCall(ef,el)) tr p

	let mk_static_field_2 c n p =
		mk_static_field c (PMap.find n c.cl_statics) p

	let mk_static_call_2 c n el p =
		mk_static_call c (PMap.find n c.cl_statics) el p

	let mk_local v p =
		{ eexpr = TLocal v; etype = v.v_type; epos = p }

	let mk_block con p el =
		let t = match List.rev el with
			| [] -> con.com.basic.tvoid
			| hd :: _ -> hd.etype
		in
		mk (TBlock el) t p

	let mk_cast e t =
		{ e with eexpr = TCast(e, None); etype = t }

	let mk_deref con p e =
		mk_static_call con.hxc.c_lib con.hxc.cf_deref [e] p

	let mk_ccode ctx s p =
		mk_static_call_2 ctx.con.hxc.c_lib "cCode" [mk (TConst (TString s)) ctx.con.com.basic.tstring p] p

	let mk_int com i p =
		mk (TConst (TInt (Int32.of_int i))) com.basic.tint p

	let debug ctx e =
		Printf.sprintf "%s: %s" ctx.fctx.field.cf_name (s_expr (s_type (print_context())) e)

	let mk_class_field name t public pos kind params =
		{
			cf_name = name;
			cf_type = t;
			cf_public = public;
			cf_pos = pos;
			cf_doc = None;
			cf_meta = [ Meta.CompilerGenerated, [], Ast.null_pos ]; (* annotate that this class field was generated by the compiler *)
			cf_kind = kind;
			cf_params = params;
			cf_expr = None;
			cf_overloads = [];
		}

	let mk_binop op e1 e2 et p =
		{ eexpr=TBinop(op,e1,e2); etype=et; epos=p }

	let mk_obj_decl fields p =
		let fields = List.sort compare fields in
		let t_fields = List.fold_left (fun acc (n,e) ->
			let cf = mk_class_field n e.etype true e.epos (Var {v_read = AccNormal; v_write = AccNormal}) [] in
			PMap.add n cf acc
		) PMap.empty fields in
		let t = TAnon {a_fields = t_fields; a_status = ref Closed} in
		mk (TObjectDecl fields) t p

	let insert_expr e once f =
		let el = match e.eexpr with TBlock el -> el | _ -> [e] in
		let el,found = List.fold_left (fun (acc,found) e ->
			match f e with
			| Some e1 when not once || not found -> e :: e1 :: acc,true
			| _ -> e :: acc,found
		) ([],false) el in
		mk (TBlock (List.rev el)) e.etype e.epos,found

	let wrap_function con ethis efunc =
		let c,t = match con.hxc.t_closure t_dynamic with TInst(c,_) as t -> c,t | _ -> assert false in
		let cf_func = PMap.find "_func" c.cl_fields in
		mk (TNew(c,[efunc.etype],[mk_cast efunc cf_func.cf_type;ethis])) t efunc.epos

	let wrap_static_function con efunc =
		wrap_function con (mk (TConst TNull) (mk_mono()) efunc.epos) efunc

	let add_meta m e =
		mk (TMeta((m,[],e.epos),e)) e.etype e.epos
end


(* Filters *)

module Filters = struct

	let add_filter con filter =
		con.filters <- filter :: con.filters

	let run_filters gen e =
		(* local vars / temp vars handling *)
		let declared_vars = ref [] in
		let temp_var_counter = ref (-1) in

		(* temporary var handling *)
		let old_declare = gen.declare_var in
		gen.declare_var <- (fun (tvar,eopt) ->
			declared_vars := (tvar,eopt) :: !declared_vars;
		);
		gen.declare_temp <- (fun t eopt ->
			incr temp_var_counter;
			let v = alloc_var ("_tmp" ^ (string_of_int !temp_var_counter)) t in
			gen.declare_var (v,eopt);
			v
		);

		let ret = List.fold_left (fun e f ->
			let run = f gen in
			let process_next_block = ref true in
			let rec map e = match e.eexpr with
				| TBlock(el) when !process_next_block ->
					let old_declared = !declared_vars in
					declared_vars := [];
					(* run loop *)
					let el = match (mk_block (run e)).eexpr with
						| TBlock el -> el
						| _ -> assert false
					in
					(* change loop with new declared vars *)
					let el = match !declared_vars with
						| [] -> el
						| vars ->
							{ eexpr = TVars(List.rev vars); etype = gen.gcom.basic.tvoid; epos = e.epos } :: el
					in
					let ret = { e with eexpr = TBlock(el) } in
					declared_vars := old_declared;
					ret
				| TBlock _ ->
					process_next_block := true;
					run e
				| _ -> run e
			in

			let last_map = gen.map in
			gen.map <- map;
			let ret = map e in
			gen.map <- last_map;
			ret
		) e gen.gcon.filters in
		gen.declare_var <- old_declare;
		ret

	let run_filters_field gen cf =
		gen.gfield <- cf;
		match cf.cf_expr with
		| None -> ()
		| Some e ->
			cf.cf_expr <- Some (run_filters gen e)

	let mk_gen_context con =
		let gen = {
			gcom = con.com;
			gcon = con;
			gfield = null_field;
			mtype = None;
			map = (function _ -> assert false);
			declare_var = (fun _ -> assert false);
			declare_temp = (fun _ _ -> assert false);
			run_filter = (fun _ -> assert false);
			add_field = (fun c cf stat ->
				if stat then
					c.cl_ordered_statics <- cf :: c.cl_ordered_statics
				else
					c.cl_ordered_fields <- cf :: c.cl_ordered_fields);
			delays = [];
		} in
		gen

	let run_filters_types con =
		let gen = mk_gen_context con in
		List.iter (fun md -> match md with
			| TClassDecl c ->
				gen.mtype <- Some md;
				let added = ref [] in
				let old_run_filter = gen.run_filter in
				gen.run_filter <- (fun cf ->
					added := cf :: !added);

				let fields = c.cl_ordered_fields in
				let statics = c.cl_ordered_statics in
				Option.may (run_filters_field gen) c.cl_constructor;
				List.iter (run_filters_field gen) fields;
				List.iter (run_filters_field gen) statics;
				gen.gfield <- null_field;
				c.cl_init <- Option.map (run_filters gen) c.cl_init;

				(* run all added fields *)
				let rec loop () = match !added with
					| [] -> ()
					| hd :: tl ->
						added := tl;
						run_filters_field gen hd;
						loop ()
				in
				loop();
				gen.run_filter <- old_run_filter
			| _ -> ()
		) con.com.types;
		gen

end

(*
	This filter will take all out-of-place TVars declarations and add to the beginning of each block.
	TPatMatch has some var names sanitized.
*)
module VarDeclarations = struct

	let filter gen = function e ->
		match e.eexpr with
		| TVars tvars ->
			let el = ExtList.List.filter_map (fun (v,eo) ->
				gen.declare_var (v,None);
				match eo with
				| None -> None
				| Some e -> Some { eexpr = TBinop(Ast.OpAssign, Expr.mk_local v e.epos, gen.map e); etype = e.etype; epos = e.epos }
			) tvars in
			(match el with
			| [e] -> e
			| _ -> Expr.mk_block gen.gcon e.epos el)
		| _ ->
			Type.map_expr gen.map e

end

(*
	Transforms (x = value) function arguments to if (x == null) x = value expressions.
	Must run before VarDeclarations or the universe implodes.
*)
module DefaultValues = struct

	let filter gen = function e ->
		match e.eexpr with
		| TFunction tf ->
			let e = List.fold_left (fun e (v,co) ->
				match co with
				| None
				| Some TNull -> e
				| Some c ->
					let eloc = Expr.mk_local v e.epos in
					let econd = Codegen.mk_parent (Codegen.binop OpEq (mk (TConst TNull) (mk_mono()) e.epos) eloc gen.gcom.basic.tbool e.epos) in
					let eassign = Codegen.binop OpAssign eloc (mk (TConst c) v.v_type e.epos) v.v_type e.epos in
					let eif = mk (TIf(econd,eassign,None)) gen.gcom.basic.tvoid e.epos in
					Codegen.concat eif e
			) tf.tf_expr tf.tf_args in
			{ e with eexpr = TFunction({tf with tf_expr = gen.map e})}
		| TCall({eexpr = TField(_,FStatic({cl_path=["haxe"],"Log"},{cf_name="trace"}))}, e1 :: {eexpr = TObjectDecl fl} :: _) when not !Analyzer.assigns_to_trace ->
			let s = match follow e1.etype with
				| TAbstract({a_path=[],"Int"},_) -> "i"
				| TInst({cl_path=[],"String"},_) -> "s"
				| _ ->
					gen.gcom.warning "This will probably not work as expected" e.epos;
					"s"
			in
			let eformat = mk (TConst (TString ("%s:%ld: %" ^ s ^ "\\n"))) gen.gcom.basic.tstring e.epos in
			let eargs = mk (TArrayDecl [List.assoc "fileName" fl;List.assoc "lineNumber" fl;e1]) (gen.gcom.basic.tarray gen.gcon.hxc.t_vararg) e.epos in
			Expr.mk_static_call_2 gen.gcon.hxc.c_cstdio "printf" [eformat;eargs] e.epos
		| _ ->
			Type.map_expr gen.map e

end


(*
	This filter handles unification cases where AST transformation may be required.
	These occur in the following nodes:

		- TBinop(OpAssign,_,_)
		- TVars
		- TCall and TNew
		- TArrayDecl
		- TObjectDecl
		- TReturn
		- TODO: TIf may be missing

	It may perform the following transformations:
		- pad TObjectDecl with null for optional arguments
		- use Array as argument list to "rest" argument
*)
module TypeChecker = struct

	let rec check gen e t =
		match e.eexpr,follow t with
		| TObjectDecl fl,(TAnon an as ta) ->
			let fields = sort_anon_fields (pmap_to_list an.a_fields) in
			let fl = List.map (fun cf ->
				try cf.cf_name,List.assoc cf.cf_name fl
				with Not_found -> cf.cf_name,mk (TConst TNull) (mk_mono()) e.epos
			) fields in
			{ e with eexpr = TObjectDecl fl; etype = ta}
		(* literal String assigned to const char* = pass through *)
		| TCall({eexpr = TField(_,FStatic({cl_path = [],"String"}, {cf_name = "ofPointerCopyNT"}))},[{eexpr = TConst (TString _)} as e]),(TAbstract({a_path = ["c"],"ConstPointer"},[TAbstract({a_path=[],"hx_char"},_)]) | TAbstract({a_path=["c"],"VarArg"},_)) ->
			e
		(* String assigned to const char* or VarArg = unwrap *)
		| _,(TAbstract({a_path=["c"],"VarArg"},_)) when (match follow e.etype with TInst({cl_path = [],"String"},_) -> true | _ -> false) ->
			Expr.mk_static_call_2 gen.gcon.hxc.c_string "raw" [e] e.epos
		| TMeta(m,e1),t ->
			{ e with eexpr = TMeta(m,check gen e1 t)}
		| TParenthesis(e1),t ->
			{ e with eexpr = TParenthesis(check gen e1 t)}
		| _ ->
			e

	let check_call_params gen el tl =
		let rec loop acc el tl = match el,tl with
			| e :: el, (n,_,t) :: tl ->
				(* check for rest argument *)
				begin match e.eexpr with
					| TArrayDecl el2 when n = "rest" && tl = [] && el = [] ->
						let ta = match follow e.etype with
							| TInst({cl_path=[],"Array"},[t]) -> t
							| _ -> t_dynamic
						in
						loop acc el2 (List.map (fun _ -> "rest",false,ta) el2)
					| _ ->
						loop ((check gen (gen.map e) t) :: acc) el tl
				end
			| [], [] ->
				acc
			| [],_ ->
				(* should not happen due to padded nulls *)
				assert false
			| _, [] ->
				(* not sure about this one *)
				assert false
		in
		List.rev (loop [] el tl)

	let fstack = ref []

	let filter gen = function e ->
		match e.eexpr with
		| TBinop(OpAssign,e1,e2) ->
			{e with eexpr = TBinop(OpAssign,gen.map e1,check gen (gen.map e2) e1.etype)}
		| TVars vl ->
			let vl = ExtList.List.filter_map (fun (v,eo) ->
				match eo with
				| None -> Some(v,None)
				| Some e ->
					Some (v,Some (check gen (gen.map e) v.v_type))
			) vl in
			{ e with eexpr = TVars(vl)}
		| TLocal v ->
			{ e with etype = v.v_type }
		| TCall(e1,el) ->
			begin match follow e1.etype with
				| TFun(args,_) | TAbstract({a_path = ["c"],"FunctionPointer"},[TFun(args,_)]) ->
					{e with eexpr = TCall(gen.map e1,check_call_params gen el args)}
				| _ -> Type.map_expr gen.map e
			end
		| TNew(c,tl,el) ->
			let tcf,_ = get_constructor (fun cf -> apply_params c.cl_types tl cf.cf_type) c in
			begin match follow tcf with
				| TFun(args,_) | TAbstract({a_path = ["c"],"FunctionPointer"},[TFun(args,_)]) ->
					{e with eexpr = TNew(c,tl,check_call_params gen el args)}
				| _ -> Type.map_expr gen.map e
			end
		| TArrayDecl el ->
			begin match follow e.etype with
				| TInst({cl_path=[],"Array"},[t]) -> {e with eexpr = TArrayDecl(List.map (fun e -> check gen (gen.map e) t) el)}
				| _ -> Type.map_expr gen.map e
			end
		| TObjectDecl fl ->
			begin match follow e.etype with
				| TAnon an ->
					let fl = List.map (fun (n,e) ->
						let t = (PMap.find n an.a_fields).cf_type in
						n,check gen (gen.map e) t
					) fl in
					{ e with eexpr = TObjectDecl fl }
				| _ -> Type.map_expr gen.map e
			end
		| TReturn (Some e1) ->
			begin match !fstack,follow gen.gfield.cf_type with
				| tf :: _,_ -> { e with eexpr = TReturn (Some (check gen (gen.map e1) tf.tf_type))}
				| [],TFun(_,tr) -> { e with eexpr = TReturn (Some (check gen (gen.map e1) tr))}
				| _,t -> assert false
			end
		| TCast (e1,None) ->
			let t = follow e.etype in
			if e1.etype != t then
				{e with eexpr = TCast(check gen (gen.map e1) t,None)}
			else
				{e with eexpr = TCast(gen.map e1,None)}
		| TSwitch(e1,cases,def) ->
			let cases = List.map (fun (el,e) -> List.map (fun e -> check gen (gen.map e) e1.etype) el,gen.map e) cases in
			{ e with eexpr = TSwitch(e1,cases,match def with None -> None | Some e -> Some (gen.map e))}
		| TFunction tf ->
			fstack := tf :: !fstack;
			let etf = {e with eexpr = TFunction({tf with tf_expr = gen.map tf.tf_expr})} in
			fstack := List.tl !fstack;
			etf
		| TThrow e1 ->
			{ e with eexpr = TThrow (check gen e1 e1.etype) }
		| _ ->
			Type.map_expr gen.map e

end

(*
	- wraps String literals in String
	- translates String OpAdd to String.concat
	- translates String == String to String.equals
	- translates switch(String) to if-chain
*)
module StringHandler = struct
	let is_string t = match follow t with
		| TInst({cl_path = [],"String"},_) -> true
		| _ -> false

	let filter gen e =
		match e.eexpr with
		(* always wrap String literal *)
		| TCall({eexpr = TField(_,FStatic({cl_path=[],"String"},{cf_name = "raw"}))},[{eexpr = TConst(TString s)} as e]) ->
			e
		| (TConst (TString s) | TNew({cl_path=[],"String"},[],[{eexpr = TConst(TString s)}])) ->
			Expr.mk_static_call_2 gen.gcon.hxc.c_string "ofPointerCopyNT" [mk (TConst (TString s)) e.etype e.epos] e.epos
		| TBinop((OpEq | OpNotEq) as op,e1,e2) when is_string e1.etype ->
			Expr.mk_binop op
				(Expr.mk_static_call_2 gen.gcon.hxc.c_string "equals" [gen.map e1; gen.map e2] e1.epos)
				(mk (TConst (TBool true)) gen.gcom.basic.tbool e1.epos)
				e.etype
				e.epos
		| TBinop(OpAdd,e1,e2) when is_string e1.etype ->
			Expr.mk_static_call_2 gen.gcon.hxc.c_string "concat" [gen.map e1; gen.map e2] e1.epos
		| TBinop(OpAssignOp(OpAdd),e1,e2) when is_string e1.etype ->
			(* TODO: we have to cache e1 in a temp var and handle the assignment correctly *)
			Expr.mk_binop
				OpAssign
				e1
				(Expr.mk_static_call_2 gen.gcon.hxc.c_string "concat" [gen.map e1; gen.map e2] e1.epos)
				e1.etype
				e.epos
		| _ ->
			Type.map_expr gen.map e
end

module SwitchHandler = struct
	let filter gen e =
		match e.eexpr with
		| TPatMatch dt ->
			let fl = gen.gcon.num_labels in
			gen.gcon.num_labels <- gen.gcon.num_labels + (Array.length dt.dt_dt_lookup) + 1;
			let i_last = Array.length dt.dt_dt_lookup in
			let mk_label_expr i = mk (TConst (TInt (Int32.of_int (i + fl)))) gen.gcom.basic.tint e.epos in
			let mk_label_meta i =
				let elabel = mk_label_expr i in
				Expr.add_meta (Meta.Custom ":label") elabel
			in
			let mk_goto_meta i =
				let elabel = mk_label_expr i in
				Expr.add_meta (Meta.Custom ":goto") elabel
			in
			let check_var_name v =
				if v.v_name.[0] = '`' then v.v_name <- "_" ^ (String.sub v.v_name 1 (String.length v.v_name - 1));
			in
			let rec mk_dt dt =
				match dt with
				| DTExpr e ->
					let egoto = mk_goto_meta i_last in
					Codegen.concat e egoto
				| DTGuard(e1,dt,dto) ->
					let ethen = mk_dt dt in
					let eelse = match dto with None -> None | Some dt -> Some (mk_dt dt) in
					mk (TIf(Codegen.mk_parent e1,ethen,eelse)) ethen.etype (punion e1.epos ethen.epos)
				| DTBind(vl,dt) ->
					let vl = List.map (fun ((v,_),e) ->
						check_var_name v;
						v,Some e
					) vl in
					let evars = mk (TVars vl) gen.gcom.basic.tvoid e.epos in
					Codegen.concat evars (mk_dt dt)
				| DTGoto i ->
					mk_goto_meta i
				| DTSwitch(e1,cl,dto) ->
					let cl = List.map (fun (e,dt) -> [e],mk_dt dt) cl in
					let edef = match dto with None -> None | Some dt -> Some (mk_dt dt) in
					mk (TSwitch(e1,cl,edef)) t_dynamic e.epos
			in
			let el,i = Array.fold_left (fun (acc,i) dt ->
				let elabel = mk_label_meta i in
				let edt = mk_dt dt in
				(Codegen.concat elabel edt) :: acc,i + 1
			) ([],0) dt.dt_dt_lookup in
			let e = gen.map (Expr.mk_block gen.gcon e.epos el) in
			let e = Expr.add_meta (Meta.Custom ":patternMatching") e in
			List.iter (fun (v,_) -> check_var_name v) dt.dt_var_init;
			let einit = mk (TVars dt.dt_var_init) gen.gcom.basic.tvoid e.epos in
			let elabel = mk_label_meta i in
			let e1 = Codegen.concat einit (Codegen.concat e elabel) in
			if dt.dt_first = i - 1 then
				e1
			else
				Codegen.concat (mk_goto_meta dt.dt_first) e1
		| TSwitch(e1,cases,def) when StringHandler.is_string e1.etype ->
			let length_map = Hashtbl.create 0 in
			List.iter (fun (el,e) ->
				List.iter (fun es ->
					match es.eexpr with
					| TConst (TString s) ->
						let l = String.length s in
						let sl = try
							Hashtbl.find length_map l
						with Not_found ->
							let sl = ref [] in
							Hashtbl.replace length_map l sl;
							sl
						in
						sl := ([es],e) :: !sl;
					| _ ->
						()
				) el
			) cases;
			let mk_eq e1 e2 = mk (TBinop(OpEq,e1,e2)) gen.gcon.com.basic.tbool (punion e1.epos e2.epos) in
			let mk_or e1 e2 = mk (TBinop(OpOr,e1,e2)) gen.gcon.com.basic.tbool (punion e1.epos e2.epos) in
			let mk_if (el,e) eo =
				let eif = List.fold_left (fun eacc e -> mk_or eacc (mk_eq e1 e)) (mk_eq e1 (List.hd el)) (List.tl el) in
				mk (TIf(Codegen.mk_parent eif,e,eo)) e.etype e.epos
			in
			let cases = Hashtbl.fold (fun i el acc ->
				let eint = mk (TConst (TInt (Int32.of_int i))) gen.gcom.basic.tint e.epos in
				let fs = match List.fold_left (fun eacc ec -> Some (mk_if ec eacc)) def !el with Some e -> e | None -> assert false in
				([eint],fs) :: acc
			) length_map [] in
 			let c_string = match gen.gcom.basic.tstring with TInst(c,_) -> c | _ -> assert false in
			let cf_length = PMap.find "length" c_string.cl_fields in
			let ef = mk (TField(e1,FInstance(c_string,cf_length))) gen.gcom.basic.tint e.epos in
			let e = mk (TSwitch(Codegen.mk_parent ef,cases,None)) t_dynamic e.epos in
			gen.map e
		| _ ->
				Type.map_expr gen.map e
end


(*
	This filter turns all non-top TFunction nodes into class fields and creates a c.Closure object
	in their place.

	It also handles calls to closures, i.e. local variables and Var class fields.
*)
module ClosureHandler = struct
	let fstack = ref []

	let ctx_name = "_ctx"

	let mk_closure_field gen tf ethis p =
		let locals = ref PMap.empty in
		let unknown = ref PMap.empty in
		let save_locals () =
			let old = !locals in
			fun () -> locals := old
		in
		let add_local v = if not (PMap.mem v.v_name !locals) then locals := PMap.add v.v_name v !locals in
		let add_unknown v = if not (PMap.mem v.v_name !unknown) then unknown := PMap.add v.v_name v !unknown in
		List.iter (fun (v,_) -> add_local v) tf.tf_args;
		let v_this = alloc_var "this" t_dynamic in
		let t_ctx = mk_mono() in
		let v_ctx = alloc_var ctx_name t_ctx in
		let e_ctx = mk (TLocal v_ctx) v_ctx.v_type p in
		let mk_ctx_field v =
			let ef = mk (TField(e_ctx,FDynamic v.v_name)) v.v_type p in
			Expr.mk_cast ef v.v_type
		in
		let rec loop e = match e.eexpr with
			| TVars vl ->
				let vl = List.map (fun (v,eo) ->
					add_local v;
					v,match eo with None -> None | Some e -> Some (loop e)
				) vl in
				{ e with eexpr = TVars vl }
			| TLocal v ->
				if not (PMap.mem v.v_name !locals) then begin
					add_unknown v;
					mk_ctx_field v;
				end else
					e
			| TFunction tf ->
				let save = save_locals() in
				List.iter (fun (v,_) -> add_local v) tf.tf_args;
				let e = { e with eexpr = TFunction { tf with tf_expr = loop tf.tf_expr } } in
				save();
				e
			| TConst TThis ->
				if not (PMap.mem v_this.v_name !locals) then add_unknown v_this;
				mk_ctx_field v_this
			| _ ->
				Type.map_expr loop e
		in
		let e = loop tf.tf_expr in
		let name,id = alloc_temp_func gen.gcon in
		let vars,fields = PMap.fold (fun v (vars,fields) ->
			let e = match v.v_name,ethis with
				| "this",Some e -> e
				| _ -> mk (TLocal v) v.v_type p
			in
			(v :: vars),((v.v_name,e) :: fields)
		) !unknown ([],[]) in
		let eobj = Expr.mk_obj_decl fields p in
		Type.unify eobj.etype t_ctx;
		let t = TFun((ctx_name,false,eobj.etype) :: List.map (fun (v,_) -> v.v_name,false,v.v_type) tf.tf_args,tf.tf_type) in
		let cf = Expr.mk_class_field name t true p (Method MethNormal) [] in
		let tf = {
			tf_args = (v_ctx,None) :: List.map (fun v -> v,None) vars;
			tf_type = tf.tf_type;
			tf_expr = e;
		} in
		cf.cf_expr <- Some (mk (TFunction tf) e.etype e.epos);
		cf,eobj

	let add_closure_field gen c tf ethis p =
		let cf,e_init = mk_closure_field gen tf ethis p in
		gen.add_field c cf true;
		gen.run_filter cf;
		let e_field = mk (TField(e_init,FStatic(c,cf))) cf.cf_type p in
		Expr.wrap_function gen.gcon e_init e_field

	let is_call_expr = ref false
	let is_extern = ref false

	let rec is_closure_expr e =
		match e.eexpr with
			| TLocal _
			| TField(_,(FInstance(_,{cf_kind = Var _ }) | FStatic(_,{cf_kind = Var _ }))) ->
				true
			| TField(_,FAnon _) ->
				true
			| TMeta(_,e1) | TParenthesis(e1) | TCast(e1,None) ->
				is_closure_expr e1
			| _ ->
				false

	let filter gen e =
		match e.eexpr with
		| TFunction tf ->
			fstack := tf :: !fstack;
			let e1 = match !fstack,gen.mtype with
				| _ :: [],_ when (match gen.gfield.cf_kind with Method _ -> true | Var _ -> false) ->
					{e with eexpr = TFunction({tf with tf_expr = gen.map tf.tf_expr})}
				| _,Some (TClassDecl c) ->
					add_closure_field gen c tf None e.epos
				| _ ->
					assert false
			in
			fstack := List.tl !fstack;
			e1
		| _ when (match follow e.etype with 
				| TInst({cl_path=["c"],"Closure"},_) 
				| TAbstract( { a_path = ["c"],"FunctionPointer" }, _ ) -> true 
				| _ -> false) ->
			(* skip previously creates closures *)
			e
		| TCall(e1,el) ->
			let old = !is_call_expr,!is_extern in
			is_call_expr := true;
			is_extern := (match e1.eexpr with TField(_,FStatic({cl_extern = true},_)) -> true | _ -> false);
			let e1 = gen.map e1 in
			is_call_expr := fst old;
			let el = List.map gen.map el in
			let e = if not !is_extern && is_closure_expr e1 then begin
				let args,r = match follow e1.etype with TFun(args,r) | TAbstract({a_path = ["c"],"FunctionPointer"},[TFun(args,r)]) -> args,r | _ -> assert false in
				let mk_cast e = mk (TCast(e,None)) (gen.gcon.hxc.t_func_pointer e.etype) e.epos in
				let efunc = mk (TField(e1,FDynamic "_func")) (TFun(args,r)) e.epos in
				let efunc2 = {efunc with etype = TFun(("_ctx",false,t_dynamic) :: args,r)} in
				let ethis = mk (TField(e1,FDynamic "_this")) t_dynamic e.epos in
				let eif = Codegen.mk_parent (Expr.mk_binop OpNotEq ethis (mk (TConst TNull) (mk_mono()) e.epos) gen.gcom.basic.tbool e.epos) in
				let ethen = mk (TCall(mk_cast efunc2,ethis :: el)) e.etype e.epos in
				let eelse = mk (TCall(mk_cast efunc,el)) e.etype e.epos in
				let e = mk (TIf(eif,ethen,Some eelse)) e.etype e.epos in
				Expr.mk_cast e r
			end else
				{e with eexpr = TCall(e1,el)}
			in
			is_extern := snd old;
			e
		| TField(_,FStatic(c,({cf_kind = Method m} as cf))) when not !is_call_expr && not !is_extern ->
			Expr.wrap_static_function gen.gcon (Expr.mk_static_field c cf e.epos)
		| TField(e1,FClosure(Some c,{cf_expr = Some {eexpr = TFunction tf}})) ->
			add_closure_field gen c tf (Some e1) e.epos
		| _ ->
			Type.map_expr gen.map e
end

module ArrayHandler = struct

	let get_type_size tp = match tp with
	| TAbstract ( { a_path =[], "Int" } ,_ )
	| TAbstract ( { a_path =[], ("hx_int32" | "hx_uint32") } ,_ ) -> "32"
	| TAbstract ( { a_path =[], ("hx_int16" | "hx_uint16") } ,_ ) -> "16"
	| TAbstract ( { a_path =[], ("hx_int8" | "hx_uint8" | "hc_char" | "hx_uchar") } ,_ ) -> "8"
	| TAbstract ( { a_path =["c"], ("Int64" | "UInt64") } ,_ )
	| TAbstract ( {a_path = ["c"], "Pointer"}, _ ) -> "64"
	(* FIXME: should we include ConstSizeArray here? *)
	| _ -> "64"

	let rec mk_specialization_call c n suffix ethis el p =
		let name = if suffix = "" then n else n ^ "_" ^ suffix in
		begin try
			match ethis with
			| None ->
				let cf = PMap.find name c.cl_statics in
				Expr.mk_static_call c cf el p
			| Some (e,tl) ->
				let cf = PMap.find name c.cl_fields in
				let ef = mk (TField(e,FInstance(c,cf))) (apply_params c.cl_types tl cf.cf_type) p in
				mk (TCall(ef,el)) (match follow ef.etype with TFun(_,r) -> r | _ -> assert false) p
		with Not_found when suffix <> "" ->
			mk_specialization_call c n "" ethis el p
		end

	let filter gen e =
		match e.eexpr with
		(* - pointer array access -> pointer + typeref's size * index *)
		| TArray(e1, e2) ->
			begin try begin match follow e1.etype with
				| TAbstract({a_path=["c"], "ConstSizeArray"},[t;_])
				| TAbstract({a_path=["c"], "Pointer"},[t]) ->
					{e with eexpr = TArray(gen.map e1, gen.map e2)}
				| TInst(c,[tp]) ->
					let suffix = get_type_size (follow tp) in
					Expr.mk_cast (mk_specialization_call c "__get" suffix (Some(gen.map e1,[tp])) [gen.map e2] e.epos) tp
				| _ ->
					raise Not_found
			end with Not_found ->
				Expr.mk_cast (Type.map_expr gen.map e) e.etype
			end
		| TBinop( (Ast.OpAssign | Ast.OpAssignOp _ ), {eexpr = TArray(e1,e2)}, ev) ->
			(* if op <> Ast.OpAssign then assert false; FIXME: this should be handled in an earlier stage (gencommon, anyone?) *)
			begin try begin match follow e1.etype with
				| TInst(c,[tp]) ->
					let suffix = get_type_size (follow tp) in
					mk_specialization_call c "__set" suffix (Some(e1,[tp])) [gen.map e2; Expr.mk_cast (gen.map ev) tp] e.epos
				| _ ->
					raise Not_found
			end with Not_found ->
				Type.map_expr gen.map e
			end
		| TCall( ({eexpr = (TField (ethis,FInstance(c,({cf_name = cfname })))) }) ,el) ->
			begin try begin match follow ethis.etype with
				| TInst({cl_path = [],"Array"},[tp]) ->
					let suffix = get_type_size (follow tp) in
					Expr.mk_cast (mk_specialization_call c cfname suffix (Some(ethis,[tp])) el e.epos) e.etype
				| _ ->
					raise Not_found
			end with Not_found ->
				Type.map_expr gen.map e
			end
		| _ ->
			Type.map_expr gen.map e
end

(*
	- TTry is replaced with a TSwitch and uses setjmp
	- TThrow is replaced with a call to longjmp
	- TFor is replaced with TWhile
	- TArrayDecl introduces an init function which is TCalled
*)
module ExprTransformation = struct

	let mk_array_decl gen el t p =
		let tparam = match follow t with
			| TInst(_,[t]) -> t
			| _ -> assert false
		in
		let c_array = gen.gcon.hxc.c_array in
		let v = alloc_var "arr" (TInst(c_array,[tparam])) in
		let eloc = mk (TLocal v) v.v_type p in
		(*let eret = mk (TReturn (Some (Expr.mk_static_call_2 gen.gcon.hxc.c_array "ofNative" [eloc] p))) t_dynamic p in*)
		let eret = mk (TReturn (Some (eloc))) t_dynamic p in
		let (vars,einit,arity) = List.fold_left (fun (vl,el,i) e ->
			let v = alloc_var ("v" ^ (string_of_int i)) tparam in
			let e = Expr.mk_binop OpAssign (mk (TArray(eloc,Expr.mk_int gen.gcom i p)) tparam p) (mk (TLocal v) v.v_type p) tparam p in
			(v :: vl,e :: el,i + 1)
		) ([],[eret],0) el in
		let vars = List.rev vars in
		let enew = ArrayHandler.mk_specialization_call c_array "__new" (ArrayHandler.get_type_size tparam) None [Expr.mk_int gen.gcon.com arity p] p in
		(*mk (TNew(c_fixed_array,[tparam],[Expr.mk_int gen.gcon.com arity p;mk (TConst TNull) (mk_mono()) p])) t p in*)
		let evar = mk (TVars [v,Some enew]) gen.gcom.basic.tvoid p in
		let e = mk (TBlock (evar :: einit)) t p in
		let tf = {
			tf_args = List.map (fun v -> v,None) vars;
			tf_type = t;
			tf_expr = e;
		} in
		let name,id = alloc_temp_func gen.gcon in
		let tfun = TFun (List.map (fun v -> v.v_name,false,v.v_type) vars,t) in
		let cf = Expr.mk_class_field name tfun true p (Method MethNormal) [] in
		let efun = mk (TFunction tf) tfun p in
		cf.cf_expr <- Some efun;
		let c = match gen.mtype with Some (TClassDecl c) -> c | _ -> assert false in
		gen.add_field c cf true;
		gen.run_filter cf;
		Expr.mk_static_call c cf el p

	let filter gen e =
		match e.eexpr with
		| TTry (e1,cl) ->
			let p = e.epos in
			let hxc = gen.gcon.hxc in
			let epush = Expr.mk_static_call_2 hxc.c_exception "push" [] p in
			let esubj = Codegen.mk_parent (Expr.mk_static_call_2 hxc.c_csetjmp "setjmp" [Expr.mk_deref gen.gcon p epush] p) in
			let epop = Expr.mk_static_call_2 hxc.c_exception "pop" [] p in
			let loc = gen.declare_temp (hxc.t_pointer hxc.t_jmp_buf) None in
			let epopassign = mk (TVars [loc,Some epop]) gen.gcon.com.basic.tvoid p in
			let ec1,found = Expr.insert_expr (gen.map e1) true (fun e ->
				match e.eexpr with
				| TReturn _ | TBreak _ | TContinue -> Some epop
				| _ -> None
			) in
			let ec1 = if found then ec1 else Codegen.concat ec1 epop in
			let c1 = [Expr.mk_int gen.gcom 0 e.epos],ec1 in
			let def = ref None in
			let cl = c1 :: (ExtList.List.filter_map (fun (v,e) ->
				let evar = mk (TVars [v,Some (Expr.mk_static_field_2 hxc.c_exception "thrownObject" p)]) gen.gcon.com.basic.tvoid p in
				let e = Codegen.concat evar (Codegen.concat epopassign (gen.map e)) in
				if v.v_type == t_dynamic then begin
					def := Some e;
					None;
				end else
					Some ([Expr.mk_int gen.gcom (get_type_id gen.gcon v.v_type) e.epos],e)
			) cl) in
			mk (TSwitch(esubj,cl,!def)) e.etype e.epos
		| TThrow e1 ->
			let p = e.epos in
			let eassign = Codegen.binop OpAssign (Expr.mk_static_field_2 gen.gcon.hxc.c_exception "thrownObject" p) e1 e1.etype e1.epos in
			let epeek = Expr.mk_static_call_2 gen.gcon.hxc.c_exception "peek" [] p in
			let el = [Expr.mk_deref gen.gcon p epeek;Expr.mk_int gen.gcom (get_type_id gen.gcon e1.etype) p] in
			let ejmp = Expr.mk_static_call_2 gen.gcon.hxc.c_csetjmp "longjmp" el p in
			Codegen.concat eassign ejmp
		| TArrayDecl [] ->
			let c,t = match follow (gen.gcon.com.basic.tarray (mk_mono())) with
				| TInst(c,[t]) -> c,t
				| _ -> assert false
			in
			mk (TNew(c,[t],[])) gen.gcon.com.basic.tvoid e.epos
		| TArrayDecl el ->
			mk_array_decl gen el e.etype e.epos
		| _ ->
			Type.map_expr gen.map e

end

module ExprTransformation2 = struct

	let filter gen e =
		match e.eexpr with
		| TFor(v,e1,e2) ->
			let e1 = gen.map e1 in
			let vtemp = gen.declare_temp e1.etype None in
			gen.declare_var (v,None);
			let ev = Expr.mk_local vtemp e1.epos in
			let ehasnext = mk (TField(ev,quick_field e1.etype "hasNext")) (tfun [] gen.gcon.com.basic.tbool) e1.epos in
			let ehasnext = mk (TCall(ehasnext,[])) ehasnext.etype ehasnext.epos in
			let enext = mk (TField(ev,quick_field e1.etype "next")) (tfun [] v.v_type) e1.epos in
			let enext = mk (TCall(enext,[])) v.v_type e1.epos in
			let eassign = Expr.mk_binop OpAssign (Expr.mk_local v e.epos) enext v.v_type e.epos in
			let ebody = Codegen.concat eassign (gen.map e2) in
			mk (TBlock [
				mk (TVars [vtemp,Some e1]) gen.gcom.basic.tvoid e1.epos;
				mk (TWhile((mk (TParenthesis ehasnext) ehasnext.etype ehasnext.epos),ebody,NormalWhile)) gen.gcom.basic.tvoid e1.epos;
			]) gen.gcom.basic.tvoid e.epos
		| _ ->
			Type.map_expr gen.map e
end


(* Output and context *)

let spr ctx s = Buffer.add_string ctx.buf s
let print ctx = Printf.kprintf (fun s -> Buffer.add_string ctx.buf s)

let newline ctx =
	match Buffer.nth ctx.buf (Buffer.length ctx.buf - 1) with
	| '{' | ':' | ' '
	| '}' when Buffer.length ctx.buf > 1 && Buffer.nth ctx.buf (Buffer.length ctx.buf - 2) != '"' ->
		print ctx "\n%s" ctx.tabs
	| '\t' -> ()
	| _ ->
		print ctx ";\n%s" ctx.tabs

let rec concat ctx s f = function
	| [] -> ()
	| [x] -> f x
	| x :: l ->
		f x;
		spr ctx s;
		concat ctx s f l

let open_block ctx =
	let oldt = ctx.tabs in
	ctx.tabs <- "\t" ^ ctx.tabs;
	(fun() -> ctx.tabs <- oldt)

let mk_type_context con path =
	let rec create acc = function
		| [] -> ()
		| d :: l ->
			let pdir = String.concat "/" (List.rev (d :: acc)) in
			if not (Sys.file_exists pdir) then Unix.mkdir pdir 0o755;
			create (d :: acc) l
	in
	let dir = con.com.file :: fst path in
	create [] dir;
	let buf_c = Buffer.create (1 lsl 14) in
	let buf_h = Buffer.create (1 lsl 14) in
	{
		con = con;
		file_path_no_ext = String.concat "/" dir ^ "/" ^ (snd path);
		buf = buf_h;
		buf_c = buf_c;
		buf_h = buf_h;
		tabs = "";
		type_path = path;
		fctx = {
			field = null_field;
			loop_stack = [];
			meta = [];
		};
		dependencies = PMap.empty;
	}

let path_to_file_path (pack,name) = match pack with [] -> name | _ -> String.concat "/" pack ^ "/" ^ name

let get_relative_path source target =
	let rec loop pl1 pl2 acc = match pl1,pl2 with
		| s1 :: pl1,[] ->
			loop pl1 [] (".." :: acc)
		| [],s2 :: pl2 ->
			loop [] pl2 (s2 :: acc)
		| s1 :: pl1,s2 :: pl2 ->
			if s1 = s2 then loop pl1 pl2 acc
			else (List.map (fun _ -> "..") (s1 :: pl1)) @ [s2] @ pl2
		| [],[] ->
			List.rev acc
	in
	loop (fst source) (fst target) []

let close_type_context ctx =
	ctx.con.generated_types <- ctx :: ctx.con.generated_types;
	let buf = Buffer.create (Buffer.length ctx.buf_h) in
	let spr = Buffer.add_string buf in
	let n = "_h" ^ path_to_name ctx.type_path in
	let relpath path = path_to_file_path ((get_relative_path ctx.type_path path),snd path) in
	spr (Printf.sprintf "#ifndef %s\n" n);
	spr (Printf.sprintf "#define %s\n" n);
	spr "#include <stdio.h>\n";
	spr "#include <stdlib.h>\n";
	spr "#include <string.h>\n";
	if ctx.type_path <> ([],"hxc") then spr (Printf.sprintf "#include \"%s.h\"\n" (relpath ([],"hxc")));

	PMap.iter (fun path dept ->
		let name = path_to_name path in
		match dept with
			| DCStd -> spr (Printf.sprintf "#include <%s.h>\n" (path_to_file_path path))
			| DFull -> spr (Printf.sprintf "#include \"%s.h\"\n" (relpath path))
			| DForward -> spr (Printf.sprintf "typedef struct %s %s;\n" name name);
	) ctx.dependencies;
	Buffer.add_buffer buf ctx.buf_h;
	spr "\n#endif";

	let write_if_changed filepath content =
		try
			let cur = Std.input_file ~bin:true filepath in
			if cur <> content then raise Not_found
		with Not_found | Sys_error _ ->
			let ch_h = open_out_bin filepath in
			print_endline ("Writing " ^ filepath);
			output_string ch_h content;
			close_out ch_h;
	in

	write_if_changed (ctx.file_path_no_ext ^ ".h") (Buffer.contents buf);

	let sc = Buffer.contents ctx.buf_c in
	if String.length sc > 0 then begin
		let buf = Buffer.create (Buffer.length ctx.buf_c) in
		Buffer.add_string buf ("#include \"" ^ (snd ctx.type_path) ^ ".h\"\n");
		PMap.iter (fun path dept ->
			match dept with
			| DFull | DForward ->
				Buffer.add_string buf (Printf.sprintf "#include \"%s.h\"\n" (relpath path))
			| _ -> ()
		) ctx.dependencies;
		Buffer.add_string buf sc;
		write_if_changed (ctx.file_path_no_ext ^ ".c") (Buffer.contents buf);
	end


(* Dependency handling *)

let add_dependency ctx dept path =
	if path <> ctx.type_path then ctx.dependencies <- PMap.add path dept ctx.dependencies

let parse_include com s p =
	if s.[0] = '<' then begin
		if s.[String.length s - 1] <> '>' then com.error "Invalid include directive" p;
		(* take off trailing .h because it will be added back later *)
		let i = if String.length s > 4 && s.[String.length s - 2] = 'h' && s.[String.length s - 3] = '.' then
			String.length s - 4
		else
			String.length s - 2
		in
		([],String.sub s 1 i),DCStd
	end else
		([],s),DForward

let check_include_meta ctx meta =
	try
		let _,el,p = get_meta Meta.Include meta in
		List.iter (fun e -> match fst e with
			| EConst(String s) when String.length s > 0 ->
				let path,dept = parse_include ctx.con.com s p in
				add_dependency ctx dept path
			| _ ->
				()
		) el;
		true
	with Not_found ->
		false

let add_class_dependency ctx c =
	if not (check_include_meta ctx c.cl_meta) && not c.cl_extern then
		add_dependency ctx (if Meta.has Meta.Struct c.cl_meta then DFull else DForward) c.cl_path

let add_enum_dependency ctx en =
	if not (check_include_meta ctx en.e_meta) && not en.e_extern then
		add_dependency ctx (if Meta.has Meta.Struct en.e_meta || Meta.has Meta.FlatEnum en.e_meta then DFull else DForward) en.e_path

let add_abstract_dependency ctx a =
	if not (check_include_meta ctx a.a_meta) then
		add_dependency ctx (if Meta.has Meta.Struct a.a_meta then DFull else DForward) a.a_path

let add_type_dependency ctx t = match follow t with
	| TInst(c,_) ->
		add_class_dependency ctx c
	| TEnum(en,_) ->
		add_enum_dependency ctx en
	| TAnon an ->
		add_dependency ctx DFull (["c"],ctx.con.get_anon_signature an.a_fields);
	| TAbstract(a,_) ->
		add_abstract_dependency ctx a
	| TDynamic _ ->
		add_dependency ctx DForward ([],"Dynamic")
	| _ ->
		(* TODO: that doesn't seem quite right *)
		add_dependency ctx DForward ([],"Dynamic")



module VTableHandler = struct

	(*
	let fold_map f c xs =
		let c, ys = List.fold_left ( fun (acc,ys) x ->
			let acc, y  = f acc x in acc, (y :: ys)
		) (c,[]) xs in
		c, List.rev ys
	*)
		
	type vt_t = (string, tclass_field * int * tclass) PMap.t
	
	type maps = {
		mutable next    : int;
		mutable cids    : ( string, int ) PMap.t;
		mutable count   : ( int, int ) PMap.t;
		mutable types   : ( int, tclass ) PMap.t;
		mutable vtables : ( int, vt_t ) PMap.t;
	}

	let insert_or_inc con m id  =
		if PMap.exists id m then PMap.add id ((PMap.find id m) + 1) m else (PMap.add id 0 m)

	let get_class_id m c =
		let s  = String.concat ""  ((snd c.cl_path) :: (fst c.cl_path)) in
		let id = m.next in
		if PMap.exists s m.cids
			then (PMap.find s m.cids, m)
			else (	m.cids <- PMap.add s id m.cids; m.next <- id +1; (id,m) )

	(*
	let filterin f i xs =
		let rec loop i xs acc = match xs with
		| x :: xs -> if f(x) then loop (i+1) xs ((i,x) :: acc) else loop i xs acc
		| [] -> (i,acc)
		in loop i xs [] *)

	let get_methods c = List.filter ( fun cf -> match cf.cf_kind with
			| Method (MethNormal) -> true
			| _ -> false ) c.cl_ordered_fields

	let reverse_collect c =
		let next  = ref 0 in
		let idmap = ref PMap.empty in
		let get_id n =
			if PMap.exists n !idmap then
				PMap.find n !idmap
			else
				let id = !next in
				next := !next + 1;
				idmap := PMap.add n id !idmap;
				id
		in
		let rev_chain c =
			let rec loop c acc = match c.cl_super with
			| Some (c,_) ->  loop c ( c :: acc)
			| _ -> acc
			in (loop c [c])
		in
		let rec collect super acc xs = match xs with
		| []        -> super :: acc
		| c :: tail ->
			let methods = (get_methods c) in
			let add_meta cf meta vidx =
				if (Meta.has (Meta.Custom meta) cf.cf_meta) then ()
				else (cf.cf_meta <- (Meta.Custom meta, [EConst(Int (string_of_int vidx)),cf.cf_pos], cf.cf_pos) :: cf.cf_meta)
			    in
			let add_meta_c c meta vidx = (*OMG FIXME*)
				if (Meta.has (Meta.Custom meta) c.cl_meta) then ()
				else (c.cl_meta <- (Meta.Custom meta, [EConst(Int (string_of_int vidx)),c.cl_pos], c.cl_pos) :: c.cl_meta)
			    in
			let mm = List.fold_left ( fun  m cf ->
				let vidx = (get_id cf.cf_name) in
				(add_meta_c c ":hasvtable" vidx;add_meta cf ":overridden" vidx; PMap.add cf.cf_name ( cf, vidx ,c) m )) PMap.empty methods in
			let mm = PMap.foldi ( fun k (scf,vidx,sc) mm -> 
				
				(* if PMap.mem k mm then 
					(* mark overridden method *)
					if (Meta.has (Meta.Custom ":overridden") scf.cf_meta) then 
						mm
					else (
						scf.cf_meta <- (Meta.Custom ":overridden", [EConst(Int (string_of_int vidx)),scf.cf_pos], scf.cf_pos) :: scf.cf_meta;
						mm ) *)
				if PMap.mem k mm then mm
				else PMap.add k (scf,vidx,sc) mm ) super mm 
			in
			collect mm (super :: acc) tail
		in
		let ichain = collect PMap.empty [] (rev_chain c)
		in  ichain (*print_endline (string_of_int (List.length ichain))*)

	let p_ichain xs = List.iter (fun m ->
		(   print_endline "---";
			(PMap.iter
				(fun _ (cf,midx,c) -> (Printf.printf "class: %s func: %s idx:%d\n" (snd c.cl_path) cf.cf_name midx) )
			m)
		)
	) xs

	let get_class_name cf = match cf.cf_type with
	| TInst (c,_) -> snd c.cl_path
	| _ -> assert false


	let p_methods c = (
		List.iter ( fun cf -> match cf.cf_kind with
			| Method (MethNormal) ->
				print_endline ( " methnormal: " ^ cf.cf_name )
			| _ -> ()
		) c.cl_ordered_fields;
		List.iter ( fun cf -> match cf.cf_kind with
			| Method (MethNormal) ->
				print_endline ( " override: " ^ cf.cf_name  )
			| _ -> ()
		) c.cl_overrides )

	let get_chains con tps =
		let m = List.fold_left ( fun m tp -> match tp with
			| TClassDecl c -> ( match c.cl_super with
				| Some (c1,_) ->
					let (id,m) =  (get_class_id m c)  in
					let (id1,m) =  (get_class_id m c1) in
						m.types <- PMap.add id c m.types;
						m.types <- PMap.add id1 c1 m.types;
						m.count <- (insert_or_inc con m.count id);
						m.count <- (insert_or_inc con m.count id1);
						m
				| None -> m )
			| _ -> m ) { count   = PMap.empty; 
			             types   = PMap.empty; 
						 cids    = PMap.empty; 
						 vtables = PMap.empty; 
						 next    = 0} tps in

		let add_vtable con c vtable = 
			(* helpers *)
			let clib, cstdlib = con.hxc.c_lib, con.hxc.c_cstdlib in
			let fname   = (Expr.mk_runtime_prefix "_vtable") in
			let c_vt    = con.hxc.c_vtable in
			let t_vt    = (TInst(c_vt,[])) in 
			let t_int   = con.com.basic.tint in
			let t_voidp = con.hxc.t_pointer con.com.basic.tvoid in
			let t_vtfp  = con.hxc.t_func_pointer (Type.tfun [con.com.basic.tvoid] con.com.basic.tvoid) in
			let cf_vt = Type.mk_field fname (TInst(con.hxc.c_vtable,[])) null_pos in
			let mk_ccode s  =
				Expr.mk_static_call_2 con.hxc.c_lib "cCode" [mk (TConst (TString s)) con.com.basic.tstring null_pos] null_pos in
			let mk_field c ethis n p = try
				let cf = (PMap.find n c.cl_fields) in
				mk (TField (ethis,(FInstance (c,cf)))) cf.cf_type p
			with Not_found -> assert false
			in
			c.cl_statics <- PMap.add fname cf_vt c.cl_statics;
			c.cl_ordered_statics <- cf_vt :: c.cl_ordered_statics;
			
			(* 1. add global field for the vtable pointer *)
			let e_vt = Expr.mk_static_field c cf_vt null_pos in
			
			(* 2. add vtable initialization to cl_init *)
			
			let e_slot = mk_field c_vt e_vt "slots" null_pos in
			(* 2.1. fill vtable with function pointers*)
			let (mx,l_easgn) = PMap.fold ( fun (cf,vidx,c2) (mx,acc) -> 
				let e_fp = Expr.mk_cast (Expr.mk_static_field c2 cf null_pos) t_vtfp in 
				let esetidx = Expr.mk_binop OpAssign 
					(mk (TArray(e_slot,(Expr.mk_int con.com vidx null_pos))) t_vtfp null_pos) e_fp t_vtfp null_pos in
				(max mx vidx, esetidx :: acc)
			) vtable (0,[]) in
			
			let sizeof t = Expr.mk_static_call clib con.hxc.cf_sizeof [(mk (TConst TNull) t null_pos)] null_pos in
			let vt_size = mx+1 in
			let e_vtsize = (Expr.mk_int con.com vt_size null_pos) in
			(* sizeof(vtable_t) + vt_size * sizeof(void ( * )())  *)
			(* 2.2 allocate vtable struct (after 2.1 because we have the vtable size now) *)
			let e_allocsize  = 
				Expr.mk_binop OpAdd (mk_ccode "sizeof(c_VTable)") (
					Expr.mk_binop OpMult e_vtsize (sizeof t_vtfp) t_int null_pos
				) t_int null_pos in
			let e_alloc = Expr.mk_static_call_2 cstdlib "malloc" [e_allocsize] null_pos in 
			let e_assign_ptr = (Expr.mk_binop OpAssign e_vt e_alloc t_voidp null_pos) in
			let e_block =  Expr.mk_block con null_pos (e_assign_ptr :: l_easgn) in
			c.cl_init <- ( match c.cl_init with 
			| Some code -> Some (Codegen.concat e_block code)
			| None      -> Some e_block )
			
		in
						 
		let eochains =
			PMap.foldi (fun  k v acc -> if v = 0 then (PMap.find k m.types) :: acc else acc) m.count [] in
			let gcid c = 
				let (id,m) = get_class_id m c in id
			in
			let ifadd c v = if PMap.exists (gcid c) m.vtables then 
								false 
							else 
								let pm = PMap.add (gcid c) v m.vtables in
								let _ = m.vtables <- pm in 
								true
			in
			List.iter ( fun c -> (
				print_endline (  " end of chain: " ^ (snd c.cl_path)   );  
				p_methods c;
				let ichain = (reverse_collect c) in
				List.iter ( fun m ->
					PMap.iter ( fun n (cf,midx,c) -> 
						if (ifadd c m) then begin
							print_endline ( " adding field: " ^ (snd c.cl_path)  );
							let fname = (snd c.cl_path) in
							let cf_hd = Type.mk_field fname
								(TInst(con.hxc.c_vtable,[])) null_pos in
							con.hxc.c_vtable.cl_statics <- PMap.add fname cf_hd con.hxc.c_vtable.cl_statics;
							con.hxc.c_vtable.cl_ordered_statics <- cf_hd :: con.hxc.c_vtable.cl_ordered_statics;
							add_vtable con c m;
						end else () ) m 
					 ) ichain
				)
			) eochains
end

		
(* Helper *)

let rec is_value_type ctx t = match follow t with
	| TAbstract({ a_impl = None }, _) -> true
	| TInst(c,_) -> has_meta Meta.Struct c.cl_meta
	| TEnum(en,_) -> Meta.has Meta.FlatEnum en.e_meta
	| TAbstract(a,tl) ->
		if has_meta Meta.NotNull a.a_meta then
			true
		else
			is_value_type ctx (Codegen.Abstract.get_underlying_type a tl)
	| _ -> false

let begin_loop ctx =
	ctx.fctx.loop_stack <- None :: ctx.fctx.loop_stack;
	fun () ->
		match ctx.fctx.loop_stack with
		| ls :: l ->
			begin match ls with
				| None -> ()
				| Some s ->
					newline ctx;
					print ctx "%s: {}" s
			end;
			ctx.fctx.loop_stack <- l;
		| _ ->
			assert false

let get_native_name meta =
	try begin
		match Meta.get Meta.Native meta with
			| _,[EConst (String s),_],_ -> Some s
			| _,_,_ -> None
	end with Not_found ->
		None

let full_field_name c cf =
	if Meta.has Meta.Plain cf.cf_meta then cf.cf_name
	else match get_native_name cf.cf_meta with
		| Some n -> n
		| None -> (path_to_name c.cl_path) ^ "_" ^ cf.cf_name

let full_enum_field_name en ef = (path_to_name en.e_path) ^ "_" ^ ef.ef_name

let monofy_class c = TInst(c,List.map (fun _ -> mk_mono()) c.cl_types)

let keywords =
	let h = Hashtbl.create 0 in
	List.iter (fun s -> Hashtbl.add h s ()) [
		"auto";"break";"case";"char";"const";"continue";" default";"do";"double";
		"else";"enum";"extern";"float";"for";"goto";"if";"int";
		"long";"register";"return";"short";"signed";"sizeof";"static";"struct";
		"switch";"typedef";"union";"unsigned";"void";"volatile";"while";
	];
	h

let escape_name n =
	if Hashtbl.mem keywords n then "hx_" ^ n else n

(* Type signature *)

let rec s_type ctx t =
	match follow t with
	| TAbstract({a_path = [],"Int"},[]) -> "int"
	| TAbstract({a_path = [],"Float"},[]) -> "double"
	| TAbstract({a_path = [],"Void"},[]) -> "void"
	| TAbstract({a_path = ["c"],"Pointer"},[t]) -> (match follow t with
		| TInst({cl_kind = KTypeParameter _},_) ->
			"char*" (* we will manipulate an array of type parameters like an array of bytes *)
		| _ -> s_type ctx t ^ "*")
	| TAbstract({a_path = ["c"],"ConstPointer"},[t]) -> "const " ^ (s_type ctx t) ^ "*"
	| TAbstract({a_path = ["c"],"FunctionPointer"},[TFun(args,ret) as t]) ->
		add_type_dependency ctx (ctx.con.hxc.t_closure t);
		Printf.sprintf "%s (*)(%s)" (s_type ctx ret) (String.concat "," (List.map (fun (_,_,t) -> s_type ctx t) args))
	| TInst(({cl_path = [],"typeref"} as c),_) ->
		add_class_dependency ctx c;
		"const " ^ (path_to_name c.cl_path) ^ "*"
	| TAbstract({a_path = [],"Bool"},[]) -> "int"
	| TAbstract( a, tps ) when Meta.has (Meta.Custom ":int") a.a_meta ->
		let (meta,el,epos) = Meta.get (Meta.Custom ":int") a.a_meta in
		(match el with
			| [(EConst (String s),_)] -> ( match s with
			| "int64" -> "hx_int64"
			| "int32" -> "hx_int32"
			| "int16" -> "hx_int16"
			| "int8"  -> "hx_int8"
			| "uint64" -> "hx_uint64"
			| "uint32" -> "hx_uint32"
			| "uint16" -> "hx_uint16"
			| "uint8" -> "hx_uint8"
			| _ -> s)
			| _ -> assert false;
	)
	| TInst({cl_kind = KTypeParameter _} as c,_) ->
		(* HACK HACK HACK HACK *)
		if c.cl_path = (["c";"TypeReference"],"T") then "const void*"
		else "void*"
	| TInst(c,_) ->
		let ptr = if is_value_type ctx t then "" else "*" in
		add_class_dependency ctx c;
		(path_to_name c.cl_path) ^ ptr
	| TEnum(en,_) ->
		let ptr = if is_value_type ctx t then "" else "*" in
		add_enum_dependency ctx en;
		(path_to_name en.e_path) ^ ptr
	| TAbstract(a,_) when Meta.has Meta.Native a.a_meta ->
		let ptr = if is_value_type ctx t then "" else "*" in
		(path_to_name a.a_path) ^ ptr
	| TAnon a ->
		begin match !(a.a_status) with
		| Statics c -> "Class_" ^ (path_to_name c.cl_path) ^ "*"
		| EnumStatics en -> "Enum_" ^ (path_to_name en.e_path) ^ "*"
		| AbstractStatics a -> "Anon_" ^ (path_to_name a.a_path) ^ "*"
		| _ ->
			let signature = ctx.con.get_anon_signature a.a_fields in
			add_dependency ctx DFull (["c"],signature);
			"c_" ^ signature ^ "*"
		end
	| TFun(args,ret) ->
		let t = ctx.con.hxc.t_closure t in
		add_type_dependency ctx t;
		s_type ctx t
	| _ -> "void*"

let rec s_type_with_name ctx t n =
	match follow t with
	| TFun(args,ret) ->
		let t = ctx.con.hxc.t_closure t in
		add_type_dependency ctx t;
		s_type_with_name ctx t n
	| TAbstract({a_path = ["c"],"Pointer"},[t]) -> ( s_type_with_name ctx t ("*" ^ n))
	| TAbstract({a_path = ["c"],"FunctionPointer"},[TFun(args,ret) as t]) ->
		add_type_dependency ctx (ctx.con.hxc.t_closure t);
		Printf.sprintf "%s (*%s)(%s)" (s_type ctx ret) (escape_name n) (String.concat "," (List.map (fun (_,_,t) -> s_type ctx t) args))
	| TAbstract({a_path = ["c"],"ConstSizeArray"},[t;const]) ->
		let size = match follow const with
			| TInst({ cl_path=[],name },_) when String.length name > 1 && String.get name 0 = 'I' ->
				String.sub name 1 (String.length name - 1)
			| _ ->
				"1"
		in
		(s_type_with_name ctx t ((escape_name n) ^ "["^ size ^"]"))
	| _ ->
		(s_type ctx t) ^ " " ^ (escape_name n)


(* Expr generation *)

let rec generate_call ctx e need_val e1 el = match e1.eexpr,el with
	| TField(_,FStatic({cl_path = ["c"],"Lib"}, cf)),(e1 :: el) ->
		begin match cf.cf_name with
		| "getAddress" ->
			spr ctx "&(";
			generate_expr ctx true e1;
			spr ctx ")"
		| "dereference" ->
			if not need_val then generate_expr ctx true e1
			else begin
				spr ctx "*(";
				generate_expr ctx true e1;
				spr ctx ")"
			end
		| "sizeof" ->
			(* get TypeReference's type *)
			let t = match follow e1.etype with
				| TInst({cl_path = [],"typeref"},[t]) -> follow t
				| t -> t
			in
			print ctx "sizeof(%s)" (s_type ctx t);
		| "alloca" ->
			spr ctx "ALLOCA(";
			generate_expr ctx true e1;
			spr ctx ")"
		| "cCode" ->
			let code = match e1.eexpr with
				| TConst (TString s) -> s
				| TCast ({eexpr = TConst (TString s) },None) -> s
				| TCall({eexpr = TField(_,FStatic({cl_path = [],"String"},
					{cf_name = "ofPointerCopyNT"}))},
					[{eexpr = TConst (TString s)}]) -> s
				| _ ->
				let _ = print_endline (s_expr (Type.s_type (print_context())) e1 ) in
				assert false
			in
			spr ctx code;
		| _ ->
			ctx.con.com.error ("Unknown Lib function: " ^ cf.cf_name) e.epos
		end
	| TField(_,FStatic({cl_path = ["c"],"Lib"}, {cf_name="callMain"})),[] ->
		begin match ctx.con.com.main with
			| Some e -> generate_expr ctx false e
			| None -> ()
		end
	| TField(_,FStatic(c,({cf_name = name} as cf))),el when Meta.has Meta.Plain cf.cf_meta ->
		ignore(check_include_meta ctx c.cl_meta);
		print ctx "%s(" name;
		concat ctx "," (generate_expr ctx true) el;
		spr ctx ")";
	| TField(_,FStatic(_,cf)),el when Meta.has Meta.Native cf.cf_meta ->
		let name = match get_native_name cf.cf_meta with
			| Some s -> s
			| None -> ctx.con.com.error "String argument expected for @:native" e.epos; "_"
		in
		print ctx "%s(" name;
		concat ctx "," (generate_expr ctx true) el;
		spr ctx ")";
	| TField(e1,FInstance(c,cf)), el ->
		add_class_dependency ctx c;
		let _ = if not (Meta.has (Meta.Custom ":overridden") cf.cf_meta) then
			spr ctx (full_field_name c cf)
		else
			let (meta,el,epos) = Meta.get (Meta.Custom ":overridden") cf.cf_meta in
			(match (meta,el,pos) with
			| (_,[EConst(Int idx),p],_) -> 
				let oldbuf = ctx.buf in
				let buf = Buffer.create 0 in ctx.buf <- buf; generate_expr ctx true e1; (*TODO don't be lazy*)
				let s = Buffer.contents buf in
				let _ = ctx.buf <- oldbuf in 
				let s = s ^ "->" ^ (Expr.mk_runtime_prefix "vtable") ^ "->slots["^idx^"]" in
				let ecode = Expr.mk_ccode ctx s null_pos in
				let t_this = match cf.cf_type with 
				| TFun (ts, r) -> TFun ( ("",false,(ctx.con.hxc.t_pointer e1.etype))  :: ts, r )
				| _ -> assert false
				in
				let cast = Expr.mk_cast ecode (ctx.con.hxc.t_func_pointer t_this) in
				generate_expr ctx true cast
			| _ -> assert false )
		in
		spr ctx "(";
		generate_expr ctx true e1;
		List.iter (fun e ->
			spr ctx ",";
			generate_expr ctx true e
		) el;
		spr ctx ")"
	| TField(_,FEnum(en,ef)),el ->
		print ctx "new_%s(" (full_enum_field_name en ef);
		concat ctx "," (generate_expr ctx true) el;
		spr ctx ")"
	| _ ->
		generate_expr ctx true e1;
		spr ctx "(";
		concat ctx "," (generate_expr ctx true) el;
		spr ctx ")"

and generate_constant ctx e = function
	| TString s ->
		print ctx "\"%s\"" s;
	| TInt i ->
		print ctx "%ld" i
	| TFloat s ->
		print ctx "%s" s
	| TNull ->
		spr ctx "NULL"
	| TSuper ->
		(* TODO: uhm... *)
		()
	| TBool true ->
		spr ctx "1"
	| TBool false ->
		spr ctx "0"
	| TThis ->
		spr ctx "this"

and generate_expr ctx need_val e = match e.eexpr with
	| TConst c ->
		generate_constant ctx e c
	| TArray(e1, e2) ->
		generate_expr ctx need_val e1;
		spr ctx "[";
		generate_expr ctx true e2;
		spr ctx "]"
	| TBlock([])  ->
		if need_val then spr ctx "{ }"
	| TBlock el when need_val ->
		spr ctx "(";
		concat ctx "," (generate_expr ctx true) el;
		spr ctx ")"
	| TBlock(el) ->
		spr ctx "{";
		let b = open_block ctx in
		List.iter (fun e ->
			newline ctx;
			generate_expr ctx false e;
		) el;
		b();
		newline ctx;
		spr ctx "}";
	| TCall(e1,el) ->
		generate_call ctx e true e1 el
	| TTypeExpr (TClassDecl c) ->
		spr ctx (path_to_name c.cl_path);
	| TTypeExpr (TEnumDecl e) ->
		add_enum_dependency ctx e;
		spr ctx (path_to_name e.e_path);
	| TTypeExpr (TTypeDecl _ | TAbstractDecl _) ->
		(* shouldn't happen? *)
		assert false
	| TField(_,FStatic(c,cf)) ->
		add_class_dependency ctx c;
		spr ctx (full_field_name c cf)
	| TField(_,FEnum(en,ef)) when Meta.has Meta.FlatEnum en.e_meta ->
		spr ctx (full_enum_field_name en ef)
	| TField(_,FEnum(en,ef)) ->
		add_enum_dependency ctx en;
		print ctx "new_%s()" (full_enum_field_name en ef)
	| TField(e1,FDynamic "index") when (match follow e1.etype with TEnum(en,_) -> Meta.has Meta.FlatEnum en.e_meta | _ -> false) ->
		generate_expr ctx need_val e1
	| TField(e1,fa) ->
		let n = field_name fa in
		spr ctx "(";
		generate_expr ctx true e1;
		if is_value_type ctx e1.etype then
			print ctx ").%s" (escape_name n)
		else
			print ctx ")->%s" (escape_name n)
	| TLocal v ->
		spr ctx (escape_name v.v_name);
	| TObjectDecl fl ->
		let s = match follow e.etype with
			| TAnon an ->
				let signature = ctx.con.get_anon_signature an.a_fields in
				add_dependency ctx DFull (["c"],signature);
				signature
			| _ -> assert false
		in
		print ctx "new_c_%s(" s;
		concat ctx "," (generate_expr ctx true) (List.map (fun (_,e) -> add_type_dependency ctx e.etype; e) fl);
		spr ctx ")";
	| TNew(c,tl,el) ->
		add_class_dependency ctx c;
		spr ctx (full_field_name c (match c.cl_constructor with None -> assert false | Some cf -> cf));
		spr ctx "(";
		concat ctx "," (generate_expr ctx true) el;
		spr ctx ")";
	| TReturn None ->
		spr ctx "return"
	| TReturn (Some e1) ->
		spr ctx "return ";
		generate_expr ctx true e1;
	| TVars(vl) ->
		let f (v,eo) =
			spr ctx (s_type_with_name ctx v.v_type v.v_name);
			begin match eo with
				| None -> ()
				| Some e ->
					spr ctx " = ";
					generate_expr ctx true e;
			end
		in
		concat ctx ";" f vl
	| TWhile(e1,e2,NormalWhile) ->
		spr ctx "while";
		generate_expr ctx true e1;
		let l = begin_loop ctx in
		generate_expr ctx false (mk_block e2);
		l()
	| TWhile(e1,e2,DoWhile) ->
		spr ctx "do";
		let l = begin_loop ctx in
		generate_expr ctx false (mk_block e2);
		spr ctx " while";
		generate_expr ctx true e1;
		l()
	| TContinue ->
		spr ctx "continue";
	| TMeta((Meta.Custom ":really",_,_), {eexpr = TBreak}) ->
		spr ctx "break";
	| TMeta((Meta.Custom ":goto",_,_), {eexpr = TConst (TInt i)}) ->
		print ctx "goto hx_label_%ld" i
	| TMeta((Meta.Custom ":label",_,_), {eexpr = TConst (TInt i)}) ->
		print ctx "hx_label_%ld: {}" i
	| TBreak ->
		let label = match ctx.fctx.loop_stack with
			| (Some s) :: _ -> s
			| None :: l ->
				let s = Printf.sprintf "_hx_label%i" ctx.con.num_labels in
				ctx.con.num_labels <- ctx.con.num_labels + 1;
				ctx.fctx.loop_stack <- (Some s) :: l;
				s
			| [] ->
				assert false
		in
		print ctx "goto %s" label;
	| TIf(e1,e2,Some e3) when need_val ->
		spr ctx "(";
		generate_expr ctx true e1;
		spr ctx " ? ";
		generate_expr ctx true e2;
		spr ctx " : ";
		generate_expr ctx true e3;
		spr ctx ")"
	| TIf(e1,e2,e3) ->
		spr ctx "if";
		generate_expr ctx true e1;
		generate_expr ctx false (mk_block e2);
		begin match e3 with
			| None -> ()
			| Some e3 ->
				spr ctx " else ";
				generate_expr ctx false (mk_block e3)
		end
	| TSwitch(e1,cases,edef) ->
		spr ctx "switch";
		generate_expr ctx true e1;
		spr ctx "{";
		let generate_case_expr e =
			let e = if Meta.has (Meta.Custom ":patternMatching") ctx.fctx.meta then e
			else Codegen.concat e (Expr.add_meta (Meta.Custom ":really") (mk TBreak e.etype e.epos)) in
			generate_expr ctx false e
		in
		let b = open_block ctx in
		List.iter (fun (el,e) ->
			newline ctx;
			spr ctx "case ";
			concat ctx "," (generate_expr ctx true) el;
			spr ctx ": ";
			generate_case_expr e;
		) cases;
		begin match edef with
			| None -> ()
			| Some e ->
				newline ctx;
				spr ctx "default: ";
				generate_case_expr e;
		end;
		b();
		newline ctx;
		spr ctx "}";
	| TBinop(OpAssign,e1,e2) ->
		generate_expr ctx need_val e1;
		spr ctx " = ";
		generate_expr ctx true e2;
	| TBinop(op,e1,e2) ->
		generate_expr ctx true e1;
		print ctx " %s " (match op with OpUShr -> ">>" | _ -> s_binop op);
		generate_expr ctx true e2;
	| TUnop(op,Prefix,e1) ->
		spr ctx (s_unop op);
		generate_expr ctx true e1;
	| TUnop(op,Postfix,e1) ->
		generate_expr ctx true e1;
		spr ctx (s_unop op);
	| TParenthesis e1 ->
		spr ctx "(";
		generate_expr ctx need_val e1;
		spr ctx ")";
	| TMeta(m,e) ->
		ctx.fctx.meta <- m :: ctx.fctx.meta;
		let e1 = generate_expr ctx need_val e in
		ctx.fctx.meta <- List.tl ctx.fctx.meta;
		e1
	| TCast(e1,_) when not need_val ->
		generate_expr ctx need_val e1
	| TCast(e1,_) ->
		begin match follow e1.etype with
		| TInst(c,_) when Meta.has Meta.Struct c.cl_meta -> generate_expr ctx true e1;
		| TAbstract({a_path = ["c"],"Pointer"},[t]) when ((s_type ctx e.etype) = "int") -> generate_expr ctx true e1;
		| _ ->
			print ctx "((%s) (" (s_type ctx e.etype);
			generate_expr ctx true e1;
			spr ctx "))"
		end
	| TEnumParameter (e1,ef,i) ->
		generate_expr ctx true e1;
		begin match follow e1.etype with
			| TEnum(en,_) ->
				add_enum_dependency ctx en;
				let s,_,_ = match ef.ef_type with TFun(args,_) -> List.nth args i | _ -> assert false in
				print ctx "->args.%s.%s" ef.ef_name s;
			| _ ->
				assert false
		end
	| TArrayDecl _ | TTry _ | TFor _ | TThrow _ | TFunction _ | TPatMatch _ ->
		(* removed by filters *)
		assert false


(* Type generation *)

let generate_function_header ctx c cf stat =
	let args,ret,s = match follow cf.cf_type with
		| TFun(args,ret) -> args,ret,full_field_name c cf
		| TAbstract({a_path = ["c"],"Pointer"},[t]) ->
			begin match follow t with
				| TFun(args,ret) -> args,ret,"(*" ^ (full_field_name c cf) ^ ")"
				| _ -> assert false
			end
		| _ -> assert false
	in
	let sargs = List.map (fun (n,_,t) -> s_type_with_name ctx t n) args in
	let sargs = if stat then sargs else (s_type_with_name ctx (monofy_class c) "this") :: sargs in
	print ctx "%s(%s)" (s_type_with_name ctx ret s) (String.concat "," sargs)

let get_typeref_forward ctx path =
	Printf.sprintf "extern const typeref %s__typeref" (path_to_name path)

let generate_typedef_declaration ctx t =
	let path = Expr.t_path t in
	if is_value_type ctx t then
		print ctx "const %s %s__default = { 0 }; //default" (s_type ctx t) (path_to_name path)
	else
		print ctx "const void* %s__default = NULL; //default" (path_to_name path);
	newline ctx;
	let nullval = Printf.sprintf "&%s__default" (path_to_name path) in
	Printf.sprintf "const typeref %s__typeref = { \"%s\", %s, sizeof(%s) }; //typeref declaration" (path_to_name path) (s_type_path path) nullval (s_type ctx t)

let generate_method ctx c cf stat =
	let e = match cf.cf_expr with
		| None -> None
		| Some {eexpr = TFunction tf} -> Some tf.tf_expr
		| Some e -> Some e
	in
	ctx.fctx <- {
		field = cf;
		loop_stack = [];
		meta = [];
	};
	let rec loop e = match e.eexpr with
		| TBlock [{eexpr = TBlock _} as e1] ->
			loop e1
		| _ ->
			Type.map_expr loop e
	in
	generate_function_header ctx c cf stat;
	begin match e with
		| None -> ()
		| Some e -> match loop e with
			| {eexpr = TBlock [] } -> spr ctx "{ }"
			| e -> generate_expr ctx false e
	end;
	newline ctx;
	spr ctx "\n"

	
(*let mk_class_field name t public pos kind params =*)
let generate_header_fields ctx = 
	let v = Var {v_read=AccNormal;v_write=AccNormal} in
	let cf_vt = Expr.mk_class_field (Expr.mk_runtime_prefix "vtable" )
		(TInst(ctx.con.hxc.c_vtable,[])) false null_pos v [] in
	let cf_hd = Expr.mk_class_field (Expr.mk_runtime_prefix "header" )
		(ctx.con.hxc.t_int64 t_dynamic) false null_pos v [] in
	[cf_vt;cf_hd]
	

	
let generate_class ctx c =
	let vars = DynArray.create () in
	let svars = DynArray.create () in
	let methods = DynArray.create () in

	(* split fields into member vars, static vars and functions *)
	List.iter (fun cf -> match cf.cf_kind with
		| Var _ -> DynArray.add vars cf
		| Method m ->  DynArray.add methods (cf,false)
	) c.cl_ordered_fields;
	List.iter (fun cf -> match cf.cf_kind with
		| Var _ -> DynArray.add svars cf
		| Method _ -> DynArray.add methods (cf,true)
	) c.cl_ordered_statics;

	let path = path_to_name c.cl_path in
	let t_class = monofy_class c in

	List.iter(fun v -> 
		DynArray.insert vars 0 v;
		c.cl_fields <- PMap.add v.cf_name v c.cl_fields;
	) (generate_header_fields ctx);
	
	(* add constructor as function *)
	begin match c.cl_constructor with
		| None -> ()
		| Some cf ->
			match follow cf.cf_type, cf.cf_expr with
			| TFun(args,_), Some e ->
				let einit = if is_value_type ctx t_class then
					Some (Expr.mk_ccode ctx ("{0}; //semicolon") cf.cf_pos)
				else
					let p = cf.cf_pos in
					(* TODO: get rid of this *)
					let esize = Expr.mk_ccode ctx (Printf.sprintf "sizeof(%s)" path) p in
					Some (Expr.mk_static_call_2 ctx.con.hxc.c_cstdlib "calloc" [Expr.mk_int ctx.con.com 1 p;esize] p)
				in
				let loc = alloc_var "this" t_class in
				
				let e_vt = if (Meta.has (Meta.Custom ":hasvtable") c.cl_meta ) then 
					let cf_vt = try PMap.find (Expr.mk_runtime_prefix "vtable") c.cl_fields with
					Not_found -> 
					(print_endline (" >>>> " ^ ( String.concat "," (PMap.foldi ( fun k _ acc -> k :: acc ) c.cl_fields []))));
					assert false in
					let e_vt = mk (TField(Expr.mk_local loc cf.cf_pos,FInstance(c,cf_vt))) cf_vt.cf_type null_pos in
					let easgn = Expr.mk_binop OpAssign e_vt (Expr.mk_static_field_2 c (Expr.mk_runtime_prefix "_vtable") null_pos ) cf_vt.cf_type null_pos in
					[easgn]
				else [] in
				
				let einit = mk (TVars [loc,einit]) ctx.con.com.basic.tvoid cf.cf_pos in
				let ereturn = mk (TReturn (Some (Expr.mk_local loc cf.cf_pos))) t_dynamic cf.cf_pos in
				let e = match e.eexpr with
					| TFunction({tf_expr = ({eexpr = TBlock el } as ef) } as tf) ->
						{e with eexpr = TFunction ({tf with tf_expr = {ef with eexpr = TBlock(einit :: e_vt @ el @ [ereturn])}})}
					| _ -> assert false
				in
				cf.cf_expr <- Some e;
				cf.cf_type <- TFun(args, monofy_class c);
				DynArray.add methods (cf,true)
			| _ -> ()
	end;

	(* add init field as function *)
	begin match c.cl_init with
		| None -> ()
		| Some e ->
			ctx.con.init_modules <- c.cl_path :: ctx.con.init_modules;
			let t = tfun [] ctx.con.com.basic.tvoid in
			let f = mk_field "_hx_init" t c.cl_pos in
			let tf = {
				tf_args = [];
				tf_type = ctx.con.com.basic.tvoid;
				tf_expr = mk_block e;
			} in
			f.cf_expr <- Some (mk (TFunction tf) t c.cl_pos);
			DynArray.add methods (f,true)
	end;

	

	ctx.buf <- ctx.buf_c;

	(* spr ctx (generate_typedef_declaration ctx (TInst(c,List.map snd c.cl_types))); *)
	(* newline ctx; *)

	(* generate static vars *)
	if not (DynArray.empty svars) then begin
		spr ctx "\n// static vars\n";
		DynArray.iter (fun cf ->
			spr ctx (s_type_with_name ctx cf.cf_type (full_field_name c cf));
			newline ctx;
		) svars;
	end;

	spr ctx "\n";

	(* generate function implementations *)
	if not (DynArray.empty methods) then begin
		DynArray.iter (fun (cf,stat) ->
			generate_method ctx c cf stat;
		) methods;
	end;

	ctx.buf <- ctx.buf_h;

	(* generate header code *)
	List.iter (function
		| Meta.HeaderCode,[(EConst(String s),_)],_ ->
			spr ctx s
		| _ -> ()
	) c.cl_meta;

	(* forward declare class type *)
	print ctx "typedef struct %s %s" path path;
	newline ctx;

	
	
	(* generate member struct *)
	if not (DynArray.empty vars) then begin
		spr ctx "\n// member var structure\n";
		print ctx "typedef struct %s {" path;
		let b = open_block ctx in
		DynArray.iter (fun cf ->
			newline ctx;
			spr ctx (s_type_with_name ctx cf.cf_type cf.cf_name);
		) vars;
		b();
		newline ctx;
		print ctx "} %s" path;
		newline ctx;
	end else begin
		print ctx "typedef struct %s { void* dummy; } %s" path path;
		newline ctx;
	end;

	(* generate static vars *)
	if not (DynArray.empty svars) then begin
		spr ctx "\n// static vars\n";
		DynArray.iter (fun cf ->
		spr ctx (s_type_with_name ctx cf.cf_type (full_field_name c cf));
		newline ctx
    ) svars
	end;

	(* generate forward declarations of functions *)
	if not (DynArray.empty methods) then begin
		spr ctx "\n// forward declarations\n";
		DynArray.iter (fun (cf,stat) ->
			generate_function_header ctx c cf stat;
			newline ctx;
		) methods;
	end;

(* 	add_dependency ctx DForward ([],"typeref");
	spr ctx (get_typeref_forward ctx c.cl_path); *)
	newline ctx

let generate_flat_enum ctx en =
	ctx.buf <- ctx.buf_h;
	let ctors = List.map (fun s -> PMap.find s en.e_constrs) en.e_names in
	let path = path_to_name en.e_path in
	print ctx "typedef enum %s {\n\t" path;
	let f ef = spr ctx (full_enum_field_name en ef) in
	concat ctx ",\n\t" f ctors;
	print ctx "\n} %s;" path

let generate_enum ctx en =
	ctx.buf <- ctx.buf_h;
(* 	add_dependency ctx DForward ([],"typeref");
	spr ctx (get_typeref_forward ctx en.e_path); *)
	(* newline ctx; *)

	let ctors = List.map (fun s -> PMap.find s en.e_constrs) en.e_names in
	let path = path_to_name en.e_path in

	(* forward declare enum type *)
	print ctx "typedef struct %s %s" path path;
	newline ctx;

	(* generate constructor types *)
	spr ctx "// constructor structure";
	let ctors = List.map (fun ef ->
		newline ctx;
		match follow ef.ef_type with
		| TFun(args,_) ->
			let name = full_enum_field_name en ef in
			print ctx "typedef struct %s {" name;
			let b = open_block ctx in
			List.iter (fun (n,_,t) ->
				newline ctx;
				spr ctx (s_type_with_name ctx t n);
			) args;
			b();
			newline ctx;
			print ctx "} %s" name;
			ef
		| _ ->
			print ctx "typedef void* %s" (full_enum_field_name en ef);
			{ ef with ef_type = TFun([],ef.ef_type)}
	) ctors in

	(* generate enum type *)
	newline ctx;
	spr ctx "// enum structure";
	newline ctx;
	print ctx "typedef struct %s{" path;
	let b = open_block ctx in
	newline ctx;
	spr ctx "int index";
	newline ctx;
	spr ctx "union {";
	let b2 = open_block ctx in
	List.iter (fun ef ->
		newline ctx;
		print ctx "%s %s" (full_enum_field_name en ef) ef.ef_name
	) ctors;
	b2();
	newline ctx;
	spr ctx "} args";
	b();
	newline ctx;
	print ctx "} %s" (path_to_name en.e_path);
	newline ctx;

	spr ctx "// constructor forward declarations";
	List.iter (fun ef ->
		newline ctx;
		match ef.ef_type with
		| TFun(args,ret) ->
			print ctx "%s new_%s(%s)" (s_type ctx ret) (full_enum_field_name en ef) (String.concat "," (List.map (fun (n,_,t) -> s_type_with_name ctx t n) args));
		| _ ->
			assert false
	) ctors;
	newline ctx;

	ctx.buf <- ctx.buf_c;
	(* spr ctx (generate_typedef_declaration ctx (TEnum(en,List.map snd en.e_types))); *)
	(* newline ctx; *)

	(* generate constructor functions *)
	spr ctx "// constructor functions";
	List.iter (fun ef ->
		newline ctx;
		match ef.ef_type with
		| TFun(args,ret) ->
			print ctx "%s new_%s(%s) {" (s_type ctx ret) (full_enum_field_name en ef) (String.concat "," (List.map (fun (n,_,t) -> Printf.sprintf "%s %s" (s_type ctx t) n) args));
			let b = open_block ctx in
			newline ctx;
			print ctx "%s* this = (%s*) malloc(sizeof(%s))" path path path;
			newline ctx ;
			print ctx "this->index = %i" ef.ef_index;
			List.iter (fun (n,_,_) ->
				newline ctx;
				print ctx "this->args.%s.%s = %s" ef.ef_name n n;
			) args;
			newline ctx;
			spr ctx "return this";
			b();
			newline ctx;
			spr ctx "}"
		| _ ->
			assert false
	) ctors

(* let generate_typeref con t =
	let path = Expr.t_path t in
	let ctx = mk_type_context con path in
	ctx.buf <- ctx.buf_c;
	spr ctx (generate_typedef_declaration ctx t);
	newline ctx;
	ctx.buf <- ctx.buf_h;
	newline ctx;
	close_type_context ctx *)

let generate_type con mt = match mt with
	| TClassDecl c when not c.cl_extern ->
		let ctx = mk_type_context con c.cl_path  in
		generate_class ctx c;
		close_type_context ctx;
	| TEnumDecl en when not en.e_extern ->
		let ctx = mk_type_context con en.e_path  in
		if Meta.has Meta.FlatEnum en.e_meta then
			generate_flat_enum ctx en
		else
			generate_enum ctx en;
		close_type_context ctx;
	| TAbstractDecl { a_path = [],"Void" }
	| TAbstractDecl { a_path = ["c"],"ConstSizeArray" } -> ()
	| TAbstractDecl a when Meta.has Meta.CoreType a.a_meta ->
		let ctx = mk_type_context con a.a_path in
		ctx.buf <- ctx.buf_c;
		spr ctx " ";
		close_type_context ctx
	| _ ->
		()

let generate_anon con name fields =
	let ctx = mk_type_context con (["c"],name) in
	let name = "c_" ^ name in
	begin match fields with
	| [] ->
		print ctx "typedef int %s" name;
		newline ctx
	| fields ->
		spr ctx "// forward declaration";
		newline ctx;
		print ctx "typedef struct %s %s" name name;
		newline ctx;

		spr ctx "// structure";

		newline ctx;
		print ctx "typedef struct %s {" name;
		let b = open_block ctx in
		List.iter (fun cf ->
			newline ctx;
			spr ctx (s_type_with_name ctx cf.cf_type cf.cf_name);
		) fields;
		b();
		newline ctx;
		print ctx "} %s" name;
		newline ctx;
	end;

	spr ctx "// constructor forward declaration";
	newline ctx;
	print ctx "%s* new_%s(%s)" name name (String.concat "," (List.map (fun cf -> s_type_with_name ctx cf.cf_type cf.cf_name) fields));
	newline ctx;

	ctx.buf <- ctx.buf_c;

	spr ctx "// constructor definition";
	newline ctx;
	print ctx "%s* new_%s(%s) {" name name (String.concat "," (List.map (fun cf -> s_type_with_name ctx cf.cf_type cf.cf_name) fields));
	let b = open_block ctx in
	newline ctx;
	print ctx "%s* _hx_this = (%s*) malloc(sizeof(%s))" name name name;
	List.iter (fun cf ->
		newline ctx;
		print ctx "_hx_this->%s = %s" cf.cf_name cf.cf_name;
	) fields;
	newline ctx;
	spr ctx "return _hx_this";
	b();
	newline ctx;
	spr ctx "}";
	close_type_context ctx

let generate_init_file con =
	let ctx = mk_type_context con (["c"],"Init") in
	ctx.buf <- ctx.buf_c;
	print ctx "void _hx_init() {";
	let b = open_block ctx in
	List.iter (fun path ->
		add_dependency ctx DForward path;
		newline ctx;
		print ctx "%s__hx_init()" (path_to_name path);
	) con.init_modules;
	b();
	newline ctx;
	spr ctx "}";
	close_type_context ctx

let generate_make_file con =
	let relpath path = path_to_file_path path in
	let main_name = match con.com.main_class with Some path -> snd path | None -> "main" in
	let filepath = con.com.file ^ "/Makefile" in
	print_endline ("Writing " ^ filepath);
	let ch = open_out_bin filepath in
	output_string ch ("OUT = " ^ main_name ^ "\n");
	output_string ch "ifndef MSVC\n";
	output_string ch ("\tOUTFLAG := -o \n");
	output_string ch ("\tOBJEXT := o \n");
	output_string ch ("\tLDFLAGS += -lm \n");
	output_string ch ("else\n");
	output_string ch ("\tOUTFLAG := /Fo\n");
	output_string ch ("\tOBJEXT := obj\n");
	output_string ch ("\tCC := cl.exe\n");
	output_string ch ("endif\n");
	output_string ch ("all: $(OUT)\n");
	List.iter (fun ctx ->
		output_string ch (Printf.sprintf "%s.$(OBJEXT): %s.c " (relpath ctx.type_path) (relpath ctx.type_path));
		PMap.iter (fun path dept -> match dept with
			| DFull | DForward -> output_string ch (Printf.sprintf "%s.h " (relpath path))
			| _ -> ()
		) ctx.dependencies;
		output_string ch (Printf.sprintf "\n\t$(CC) $(CFLAGS) $(INCLUDES) $(OUTFLAG)%s.$(OBJEXT) -c %s.c\n\n" (relpath ctx.type_path) (relpath ctx.type_path))
	) con.generated_types;
	output_string ch "OBJECTS = ";
	List.iter (fun ctx ->
		if Buffer.length ctx.buf_c > 0 then
			output_string ch (Printf.sprintf "%s.$(OBJEXT) " (relpath ctx.type_path))
	) con.generated_types;
	output_string ch "\n\n$(OUT): $(OBJECTS)";
	output_string ch "\n\t$(CC) $(CFLAGS) $(INCLUDES) $(OBJECTS) -o $(OUT) $(LDFLAGS)\n";
	output_string ch "\n\nclean:\n\t$(RM) $(OUT) $(OBJECTS)";
	close_out ch


(* Init & main *)

let initialize_class con c =
	let add_init e = match c.cl_init with
		| None -> c.cl_init <- Some e
		| Some e2 -> c.cl_init <- Some (Codegen.concat e2 e)
	in
	let check_dynamic cf stat = match cf.cf_kind with
		| Method MethDynamic ->
			(* create implementation field *)
			let cf2 = {cf with cf_name = cf.cf_name ^ "_hx_impl"; cf_kind = Method MethNormal } in
			if stat then begin
				c.cl_ordered_statics <- cf2 :: c.cl_ordered_statics;
				c.cl_statics <- PMap.add cf2.cf_name cf2 c.cl_statics;
				let ef1 = Expr.mk_static_field c cf cf.cf_pos in
				let ef2 = Expr.mk_static_field c cf2 cf2.cf_pos in
				let ef2 = Expr.wrap_static_function con ef2 in
				add_init (Codegen.binop OpAssign ef1 ef2 ef1.etype ef1.epos);
			end else begin
				c.cl_ordered_fields <- cf2 :: c.cl_ordered_fields;
				c.cl_fields <- PMap.add cf2.cf_name cf2 c.cl_fields
			end;
			cf.cf_expr <- None;
			cf.cf_kind <- Var {v_read = AccNormal; v_write = AccNormal};
			cf.cf_type <- con.hxc.t_closure cf.cf_type;
		| _ ->
			()
	in

	let check_closure cf = match cf.cf_type with
		| TFun _ -> cf.cf_type <- con.hxc.t_closure cf.cf_type;
		| _ -> ()
	in

	List.iter (fun cf ->
		(match cf.cf_expr with Some e -> Analyzer.run e | _ -> ());
		match cf.cf_kind with
		| Var _ -> check_closure cf
		| Method m -> match cf.cf_type with
			| TFun(_) -> check_dynamic cf false;
			| _ -> assert false;
	) c.cl_ordered_fields;

	List.iter (fun cf ->
		(match cf.cf_expr with Some e -> Analyzer.run e | _ -> ());
		match cf.cf_kind with
		| Var _ ->
			check_closure cf;
			begin match cf.cf_expr with
				| None -> ()
				| Some e ->
					(* add static var initialization to cl_init *)
					let ta = TAnon { a_fields = c.cl_statics; a_status = ref (Statics c) } in
					let ethis = mk (TTypeExpr (TClassDecl c)) ta cf.cf_pos in
					let efield = Codegen.field ethis cf.cf_name cf.cf_type cf.cf_pos in
					let eassign = mk (TBinop(OpAssign,efield,e)) efield.etype cf.cf_pos in
					cf.cf_expr <- Some eassign;
					add_init eassign;
			end
		| Method _ -> check_dynamic cf true;
	) c.cl_ordered_statics

let generate com =
	let rec find_class path mtl = match mtl with
		| TClassDecl c :: _ when c.cl_path = path -> c
		| _ :: mtl -> find_class path mtl
		| [] -> assert false
	in
	let c_lib = find_class (["c"],"Lib") com.types in
	let null_func _ = assert false in
	let hxc = List.fold_left (fun acc mt -> match mt with
		| TClassDecl c ->
			begin match c.cl_path with
				| [],"typeref" -> {acc with t_typeref = fun t -> TInst(c,[t])}
				| [],"jmp_buf" -> {acc with t_jmp_buf = TInst(c,[])}
				| [],"hxc" -> {acc with c_boot = c}
				| [],"String" -> {acc with c_string = c}
				| [],"Array" -> {acc with c_array = c}
				| ["c"],"FixedArray" -> {acc with c_fixed_array = c}
				| ["c"],"Exception" -> {acc with c_exception = c}
				| ["c"],"Closure" -> {acc with t_closure = fun t -> TInst(c,[t])}
				| ["c"],"CString" -> {acc with c_cstring = c}
				| ["c"],"CStdlib" -> {acc with c_cstdlib = c}
				| ["c"],"CSetjmp" -> {acc with c_csetjmp = c}
				| ["c"],"CStdio" -> {acc with c_cstdio = c}
				| ["c"],"VTable" -> {acc with c_vtable = c}
				| _ -> acc
			end
		| TAbstractDecl a ->
			begin match a.a_path with
			| ["c"],"ConstSizeArray" ->
				a.a_meta <- (Meta.CoreType,[],Ast.null_pos) :: a.a_meta;
				acc
			| ["c"],"Pointer" ->
				a.a_meta <- (Meta.CoreType,[],Ast.null_pos) :: a.a_meta;
				{acc with t_pointer = fun t -> TAbstract(a,[t])}
			| ["c"],"ConstPointer" ->
				a.a_meta <- (Meta.CoreType,[],Ast.null_pos) :: a.a_meta;
				{acc with t_const_pointer = fun t -> TAbstract(a,[t])}
			| ["c"],"FunctionPointer" ->
				{acc with t_func_pointer = fun t -> TAbstract(a,[t])}
			| ["c"],"Int64" ->
				a.a_meta <- (Meta.CoreType,[],Ast.null_pos) :: a.a_meta;
				{acc with t_int64 = fun t -> TAbstract(a,[t])}
			| ["c"],"VarArg" ->
				{acc with t_vararg = TAbstract(a,[])}
			| _ ->
				acc
			end
		| _ ->
			acc
	) {
		c_lib = c_lib;
		cf_deref = PMap.find "dereference" c_lib.cl_statics;
		cf_addressof = PMap.find "getAddress" c_lib.cl_statics;
		cf_sizeof = PMap.find "sizeof" c_lib.cl_statics;
		t_typeref = null_func;
		t_pointer = null_func;
		t_closure = null_func;
		t_const_pointer = null_func;
		t_func_pointer = null_func;
		t_int64 = null_func;
		t_jmp_buf = t_dynamic;
		t_vararg = t_dynamic;
		c_boot = null_class;
		c_exception = null_class;
		c_string = null_class;
		c_array = null_class;
		c_fixed_array = null_class;
		c_cstring = null_class;
		c_csetjmp = null_class;
		c_cstdlib = null_class;
		c_cstdio = null_class;
		c_vtable = null_class;
	} com.types in
	let anons = ref PMap.empty in
	let added_anons = ref PMap.empty in
	let get_anon =
		let num_anons = ref 0 in
		fun fields ->
			let fields = pmap_to_list fields in
			let fields = sort_anon_fields fields in
			let id = String.concat "," (List.map (fun cf -> cf.cf_name ^ (Type.s_type (print_context()) (follow cf.cf_type))) fields) in
			let s = try
				fst (PMap.find id !anons)
			with Not_found ->
				incr num_anons;
				let s = "_hx_anon_" ^ (string_of_int !num_anons) in
				anons := PMap.add id (s,fields) !anons;
				added_anons := PMap.add id (s,fields) !added_anons;
				s
			in
			s
	in
	let con = {
		com = com;
		hxc = hxc;
		num_temp_funcs = 0;
		num_labels = 0;
		(* this has to start at 0 so the first type id is 1 *)
		num_identified_types = 0;
		type_ids = PMap.empty;
		type_parameters = PMap.empty;
		init_modules = [];
		generated_types = [];
		filters = [];
		get_anon_signature = get_anon;
	} in
	(* ascending priority *)
	let filters = [
		VarDeclarations.filter;
		ExprTransformation.filter;
		ArrayHandler.filter;
		TypeChecker.filter;
		StringHandler.filter;
		SwitchHandler.filter;
		ClosureHandler.filter;
		DefaultValues.filter;
		ExprTransformation2.filter
	] in
	List.iter (Filters.add_filter con) filters;
	List.iter (fun mt -> match mt with
		| TClassDecl c -> initialize_class con c
		| _ -> ()
	) com.types;

	VTableHandler.get_chains con com.types;

	let gen = Filters.run_filters_types con in
	List.iter (fun f -> f()) gen.delays; (* we can choose another time to run this if needed *)
	List.iter (generate_type con) com.types;
	let rec loop () =
		let anons = !added_anons in
		added_anons := PMap.empty;
		PMap.iter (fun _ (s,cfl) -> generate_anon con s cfl) anons;
		if not (PMap.is_empty !added_anons) then loop()
	in
	loop();
	generate_init_file con;
	generate_make_file con
