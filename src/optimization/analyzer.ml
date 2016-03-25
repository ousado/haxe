(*
	The Haxe Compiler
	Copyright (C) 2005-2016  Haxe Foundation

	This program is free software; you can redistribute it and/or
	modify it under the terms of the GNU General Public License
	as published by the Free Software Foundation; either version 2
	of the License, or (at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program; if not, write to the Free Software
	Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 *)

open Ast
open Type
open Common

let s_expr_pretty e = s_expr_pretty "" (s_type (print_context())) e

let rec is_true_expr e1 = match e1.eexpr with
	| TConst(TBool true) -> true
	| TParenthesis e1 -> is_true_expr e1
	| _ -> false

let map_values ?(allow_control_flow=true) f e =
	let branching = ref false in
	let efinal = ref None in
	let f e =
		if !branching then
			f e
		else begin
			efinal := Some e;
			mk (TConst TNull) e.etype e.epos
		end
	in
	let rec loop complex e = match e.eexpr with
		| TIf(e1,e2,Some e3) ->
			branching := true;
			let e2 = loop true e2 in
			let e3 = loop true e3 in
			{e with eexpr = TIf(e1,e2,Some e3)}
		| TSwitch(e1,cases,edef) ->
			branching := true;
			let cases = List.map (fun (el,e) -> el,loop true e) cases in
			let edef = Option.map (loop true) edef in
			{e with eexpr = TSwitch(e1,cases,edef)}
		| TBlock [e1] ->
			loop complex e1
		| TBlock el ->
			begin match List.rev el with
			| e1 :: el ->
				let e1 = loop true e1 in
				let e = {e with eexpr = TBlock (List.rev (e1 :: el))} in
				{e with eexpr = TMeta((Meta.MergeBlock,[],e.epos),e)}
			| [] ->
				f e
			end
		| TTry(e1,catches) ->
			branching := true;
			let e1 = loop true e1 in
			let catches = List.map (fun (v,e) -> v,loop true e) catches in
			{e with eexpr = TTry(e1,catches)}
		| TMeta(m,e1) ->
			{e with eexpr = TMeta(m,loop complex e1)}
		| TParenthesis e1 ->
			{e with eexpr = TParenthesis (loop complex e1)}
		| TBreak | TContinue | TThrow _ | TReturn _ ->
			if not allow_control_flow then raise Exit;
			e
		| _ ->
			if not complex then raise Exit;
			f e
	in
	let e = loop false e in
	e,!efinal

let can_throw e =
	let rec loop e = match e.eexpr with
		| TConst _ | TLocal _ | TTypeExpr _ | TFunction _ | TBlock _ -> ()
		| TCall _ | TNew _ | TThrow _ | TCast(_,Some _) -> raise Exit
		| TField _ | TArray _ -> raise Exit (* sigh *)
		| _ -> Type.iter loop e
	in
	try
		loop e; false
	with Exit ->
		true

let rec can_be_inlined e = match e.eexpr with
	| TConst _ -> true
	| TParenthesis e1 | TMeta(_,e1) -> can_be_inlined e1
	| _ -> false

let rec can_be_used_as_value com e =
	let rec loop e = match e.eexpr with
		| TBlock [e] -> loop e
		| TBlock _ | TSwitch _ | TTry _ -> raise Exit
		| TCall({eexpr = TConst (TString "phi")},_) -> raise Exit
		(* | TCall _ | TNew _ when (match com.platform with Cpp | Php -> true | _ -> false) -> raise Exit *)
		| TReturn _ | TThrow _ | TBreak | TContinue -> raise Exit
		| TUnop((Increment | Decrement),_,_) when com.platform = Python -> raise Exit
		| TNew _ when com.platform = Php -> raise Exit
		| TFunction _ -> ()
		| _ -> Type.iter loop e
	in
	try
		loop e;
		true
	with Exit ->
		false

let has_pure_meta meta = Meta.has Meta.Pure meta

let is_pure c cf = has_pure_meta c.cl_meta || has_pure_meta cf.cf_meta

let wrap_meta s e =
	mk (TMeta((Meta.Custom s,[],e.epos),e)) e.etype e.epos

let is_unbound v =
	Meta.has Meta.Unbound v.v_meta

let is_really_unbound v =
	v.v_name <> "`trace" && is_unbound v

let r = Str.regexp "^\\([A-Za-z0-9_]\\)+$"
let is_unbound_call_that_might_have_side_effects v el = match v.v_name,el with
	| "__js__",[{eexpr = TConst (TString s)}] when Str.string_match r s 0 -> false
	| _ -> true

let is_ref_type = function
	| TType({t_path = ["cs"],("Ref" | "Out")},_) -> true
	| TAbstract({a_path=["hl";"types"],"Ref"},_) -> true
	| _ -> false

let type_change_ok com t1 t2 =
	if t1 == t2 then
		true
	else begin
		let rec map t = match t with
			| TMono r -> (match !r with None -> t_dynamic | Some t -> map t)
			| _ -> Type.map map t
		in
		let t1 = map t1 in
		let t2 = map t2 in
		let rec is_nullable_or_whatever = function
			| TMono r ->
				(match !r with None -> false | Some t -> is_nullable_or_whatever t)
			| TType ({ t_path = ([],"Null") },[_]) ->
				true
			| TLazy f ->
				is_nullable_or_whatever (!f())
			| TType (t,tl) ->
				is_nullable_or_whatever (apply_params t.t_params tl t.t_type)
			| TFun _ ->
				false
			| TInst ({ cl_kind = KTypeParameter _ },_) ->
				false
			| TAbstract (a,_) when Meta.has Meta.CoreType a.a_meta ->
				not (Meta.has Meta.NotNull a.a_meta)
			| TAbstract (a,tl) ->
				not (Meta.has Meta.NotNull a.a_meta) && is_nullable_or_whatever (apply_params a.a_params tl a.a_this)
			| _ ->
				true
		in
		(* Check equality again to cover cases where TMono became t_dynamic *)
		t1 == t2 || match follow t1,follow t2 with
			| TDynamic _,_ | _,TDynamic _ -> false
			| _ ->
				if com.config.pf_static && is_nullable_or_whatever t1 <> is_nullable_or_whatever t2 then false
				else type_iseq t1 t2
	end

let dynarray_map f d =
	DynArray.iteri (fun i e -> DynArray.unsafe_set d i (f e)) d

let dynarray_mapi f d =
	DynArray.iteri (fun i e -> DynArray.unsafe_set d i (f i e)) d

module Config = struct
	type t = {
		optimize : bool;
		const_propagation : bool;
		copy_propagation : bool;
		code_motion : bool;
		local_dce : bool;
		fusion : bool;
		purity_inference : bool;
		dot_debug : bool;
		tail_call_elimination : bool;
	}

	let flag_const_propagation = "const_propagation"
	let flag_copy_propagation = "copy_propagation"
	let flag_code_motion = "code_motion"
	let flag_local_dce = "local_dce"
	let flag_fusion = "fusion"
	let flag_purity_inference = "purity_inference"
	let flag_ignore = "ignore"
	let flag_dot_debug = "dot_debug"
	let flag_tail_call_elimination = "tce_strict"

	let all_flags =
		List.fold_left (fun acc flag ->
			flag :: ("no_" ^ flag) :: acc
		) [] [flag_const_propagation;flag_copy_propagation;flag_code_motion;flag_local_dce;flag_fusion;flag_purity_inference;flag_ignore;flag_dot_debug]

	let has_analyzer_option meta s =
		try
			let rec loop ml = match ml with
				| (Meta.Analyzer,el,_) :: ml ->
					if List.exists (fun (e,p) ->
						match e with
							| EConst(Ident s2) when s = s2 -> true
							| _ -> false
					) el then
						true
					else
						loop ml
				| _ :: ml ->
					loop ml
				| [] ->
					false
			in
			loop meta
		with Not_found ->
			false

	let is_ignored meta =
		has_analyzer_option meta flag_ignore

	let get_base_config com =
		{
			optimize = not (Common.defined com Define.NoAnalyzer);
			const_propagation = not (Common.raw_defined com "analyzer-no-const-propagation");
			copy_propagation = not (Common.raw_defined com "analyzer-no-copy-propagation");
			code_motion = Common.raw_defined com "analyzer-code-motion";
			local_dce = not (Common.raw_defined com "analyzer-no-local-dce");
			fusion = not (Common.raw_defined com "analyzer-no-fusion") && (match com.platform with Flash | Java -> false | _ -> true);
			purity_inference = not (Common.raw_defined com "analyzer-no-purity-inference");
			dot_debug = false;
			tail_call_elimination = false;
		}

	let update_config_from_meta com config meta =
		List.fold_left (fun config meta -> match meta with
			| (Meta.Analyzer,el,_) ->
				List.fold_left (fun config e -> match fst e with
					| EConst (Ident s) when s = "no_" ^ flag_const_propagation -> { config with const_propagation = false}
					| EConst (Ident s) when s = flag_const_propagation -> { config with const_propagation = true}
					| EConst (Ident s) when s = "no_" ^ flag_copy_propagation -> { config with copy_propagation = false}
					| EConst (Ident s) when s = flag_copy_propagation -> { config with copy_propagation = true}
					| EConst (Ident s) when s = "no_" ^ flag_code_motion -> { config with code_motion = false}
					| EConst (Ident s) when s = flag_code_motion -> { config with code_motion = true}
					| EConst (Ident s) when s = "no_" ^ flag_local_dce -> { config with local_dce = false}
					| EConst (Ident s) when s = flag_local_dce -> { config with local_dce = true}
					| EConst (Ident s) when s = "no_" ^ flag_fusion -> { config with fusion = false}
					| EConst (Ident s) when s = flag_fusion -> { config with fusion = true}
					| EConst (Ident s) when s = "no_" ^ flag_purity_inference -> { config with purity_inference = false}
					| EConst (Ident s) when s = flag_purity_inference -> { config with purity_inference = true}
					| EConst (Ident s) when s = flag_dot_debug -> {config with dot_debug = true}
					| EConst (Ident s) when s = flag_tail_call_elimination -> {config with tail_call_elimination = true}
					| EConst (Ident s) when s = "no_" ^ flag_tail_call_elimination -> {config with tail_call_elimination = false}
					| _ ->
						let s = Ast.s_expr e in
						com.warning (Typecore.string_error s all_flags ("Unrecognized analyzer option: " ^ s)) (pos e);
						config
				) config el
			| (Meta.HasUntyped,_,_) ->
				{config with optimize = false}
			| _ ->
				config
		) config meta

		let get_class_config com c =
			let config = get_base_config com in
			update_config_from_meta com config c.cl_meta

		let get_field_config com c cf =
			let config = get_class_config com c in
			update_config_from_meta com config cf.cf_meta
	end

	(*
		This module rewrites some expressions to reduce the amount of special cases for subsequent analysis. After analysis
		it restores some of these expressions back to their original form.

		The following expressions are removed from the AST after `apply` has run:
		- OpBoolAnd and OpBoolOr binary operations are rewritten to TIf
		- OpAssignOp on a variable is rewritten to OpAssign
		- Prefix increment/decrement operations are rewritten to OpAssign
		- Postfix increment/decrement operations are rewritten to a TBlock with OpAssign and OpAdd/OpSub
		- `do {} while(true)` is rewritten to `while(true) {}`
		- TWhile expressions are rewritten to `while (true)` with appropriate conditional TBreak
		- TFor is rewritten to TWhile
	*)
	module TexprFilter = struct
		let apply com e =
			let rec loop e = match e.eexpr with
			| TBinop(OpBoolAnd | OpBoolOr as op,e1,e2) ->
				let e_then = e2 in
				let e_if,e_else = if op = OpBoolOr then
					mk (TUnop(Not,Prefix,e1)) com.basic.tbool e.epos,mk (TConst (TBool(true))) com.basic.tbool e.epos
				else
					e1,mk (TConst (TBool(false))) com.basic.tbool e.epos
				in
				loop (mk (TIf(e_if,e_then,Some e_else)) e.etype e.epos)
			| TBinop(OpAssignOp op,({eexpr = TLocal _} as e1),e2) ->
				let e = {e with eexpr = TBinop(op,e1,e2)} in
				loop {e with eexpr = TBinop(OpAssign,e1,e)}
			| TUnop((Increment | Decrement as op),flag,({eexpr = TLocal _} as e1)) ->
				let e_one = mk (TConst (TInt (Int32.of_int 1))) com.basic.tint e1.epos in
				let e = {e with eexpr = TBinop(OpAssignOp (if op = Increment then OpAdd else OpSub),e1,e_one)} in
				let e = if flag = Prefix then
					e
				else
					mk (TBlock [
						{e with eexpr = TBinop(OpAssignOp (if op = Increment then OpAdd else OpSub),e1,e_one)};
						{e with eexpr = TBinop((if op = Increment then OpSub else OpAdd),e1,e_one)};
					]) e.etype e.epos
				in
				loop e
			| TWhile(e1,e2,DoWhile) when is_true_expr e1 ->
				loop {e with eexpr = TWhile(e1,e2,NormalWhile)}
			| TWhile(e1,e2,flag) when not (is_true_expr e1) ->
				let p = e.epos in
				let e_break = mk TBreak t_dynamic p in
				let e_not = mk (TUnop(Not,Prefix,Codegen.mk_parent e1)) e1.etype e1.epos in
				let e_if eo = mk (TIf(e_not,e_break,eo)) com.basic.tvoid p in
				let rec map_continue e = match e.eexpr with
					| TContinue ->
						Texpr.duplicate_tvars (e_if (Some e))
					| TWhile _ | TFor _ ->
						e
					| _ ->
						Type.map_expr map_continue e
				in
				let e2 = if flag = NormalWhile then e2 else map_continue e2 in
				let e_if = e_if None in
				let e_block = if flag = NormalWhile then Type.concat e_if e2 else Type.concat e2 e_if in
				let e_true = mk (TConst (TBool true)) com.basic.tbool p in
				let e = mk (TWhile(Codegen.mk_parent e_true,e_block,NormalWhile)) e.etype p in
				loop e
			| TFor(v,e1,e2) ->
				let v' = alloc_var "tmp" e1.etype in
				let ev' = mk (TLocal v') e1.etype e1.epos in
				let t1 = (Abstract.follow_with_abstracts e1.etype) in
				let ehasnext = mk (TField(ev',quick_field t1 "hasNext")) (tfun [] com.basic.tbool) e1.epos in
				let ehasnext = mk (TCall(ehasnext,[])) com.basic.tbool ehasnext.epos in
				let enext = mk (TField(ev',quick_field t1 "next")) (tfun [] v.v_type) e1.epos in
				let enext = mk (TCall(enext,[])) v.v_type e1.epos in
				let eassign = mk (TVar(v,Some enext)) com.basic.tvoid e.epos in
				let ebody = Type.concat eassign e2 in
				let e = mk (TBlock [
					mk (TVar (v',Some e1)) com.basic.tvoid e1.epos;
					mk (TWhile((mk (TParenthesis ehasnext) ehasnext.etype ehasnext.epos),ebody,NormalWhile)) com.basic.tvoid e1.epos;
				]) com.basic.tvoid e.epos in
				loop e
			| _ ->
				Type.map_expr loop e
			in
			loop e
	end

	module Fusion = struct

		type interference_kind =
			| IKVarMod of tvar list
			| IKSideEffect
			| IKNone

		let get_interference_kind e =
			let vars = ref [] in
			let rec loop e = match e.eexpr with
				| TMeta((Meta.Pure,_,_),_) ->
					()
				| TUnop((Increment | Decrement),_,{eexpr = TLocal v}) ->
					vars := v :: !vars
				| TBinop((OpAssign | OpAssignOp _),{eexpr = TLocal v},e2) ->
					vars := v :: !vars;
					loop e2
				| TBinop((OpAssign | OpAssignOp _),_,_) | TUnop((Increment | Decrement),_,_) ->
					raise Exit
				| TCall({eexpr = TLocal v},el) when not (is_unbound_call_that_might_have_side_effects v el) ->
					List.iter loop el
				| TCall({eexpr = TField(_,FStatic(c,cf))},el) when is_pure c cf ->
					List.iter loop el
				| TNew(c,_,el) when (match c.cl_constructor with Some cf when is_pure c cf -> true | _ -> false) ->
					List.iter loop el;
				| TCall _ | TNew _ ->
					raise Exit
				| _ ->
					Type.iter loop e
			in
			try
				loop e;
				begin match !vars with
					| [] -> IKNone
					| vars -> IKVarMod vars
				end
			with Exit ->
				IKSideEffect

		let apply com config e =
			let rec block_element acc el = match el with
				| {eexpr = TBinop((OpAssign | OpAssignOp _),_,_) | TUnop((Increment | Decrement),_,_)} as e1 :: el ->
					block_element (e1 :: acc) el
				| {eexpr = TLocal _} as e1 :: el when not config.Config.local_dce ->
					block_element (e1 :: acc) el
				(* no-side-effect *)
				| {eexpr = TEnumParameter _ | TFunction _ | TConst _ | TTypeExpr _ | TLocal _} :: el ->
					block_element acc el
				(* no-side-effect composites *)
				| {eexpr = TParenthesis e1 | TMeta(_,e1) | TCast(e1,None) | TField(e1,_) | TUnop(_,_,e1)} :: el ->
					block_element acc (e1 :: el)
				| {eexpr = TArray(e1,e2) | TBinop(_,e1,e2)} :: el ->
					block_element acc (e1 :: e2 :: el)
				| {eexpr = TArrayDecl el1 | TCall({eexpr = TField(_,FEnum _)},el1)} :: el2 -> (* TODO: check e1 of FEnum *)
					block_element acc (el1 @ el2)
				| {eexpr = TObjectDecl fl} :: el ->
					block_element acc ((List.map snd fl) @ el)
				| {eexpr = TIf(e1,{eexpr = TBlock []},(Some {eexpr = TBlock []} | None))} :: el ->
					block_element acc (e1 :: el)
				| {eexpr = TBlock [e1]} :: el ->
					block_element acc (e1 :: el)
				| {eexpr = TBlock []} :: el ->
					block_element acc el
				| e1 :: el ->
					block_element (e1 :: acc) el
				| [] ->
					acc
			in
			let changed = ref false in
			let var_uses = Hashtbl.create 0 in
			let var_writes = Hashtbl.create 0 in
			let get_num_uses v =
				try Hashtbl.find var_uses v.v_id with Not_found -> 0
			in
			let get_num_writes v =
				try Hashtbl.find var_writes v.v_id with Not_found -> 0
			in
			let change map v delta =
				Hashtbl.replace map v.v_id ((try Hashtbl.find map v.v_id with Not_found -> 0) + delta);
			in
			let change_num_uses v delta =
				change var_uses v delta
			in
			let change_num_writes v delta =
				change var_writes v delta
			in
			let rec loop e = match e.eexpr with
				| TLocal v ->
					change_num_uses v 1;
				| TBinop(OpAssign,{eexpr = TLocal v},e2) ->
					change_num_writes v 1;
					loop e2
				| _ ->
					Type.iter loop e
			in
			loop e;
			let can_be_fused v e =
				let b = get_num_uses v <= 1 && get_num_writes v = 0 && can_be_used_as_value com e && (Meta.has Meta.CompilerGenerated v.v_meta || config.Config.optimize && config.Config.fusion && type_change_ok com v.v_type e.etype && v.v_extra = None) in
				(* let st = s_type (print_context()) in *)
				(* if e.epos.pfile = "src/Main.hx" then print_endline (Printf.sprintf "%s: %i %i %b %s %s (%b %b %b %b %b) -> %b" v.v_name (get_num_uses v) (get_num_writes v) (can_be_used_as_value com e) (st v.v_type) (st e.etype) (Meta.has Meta.CompilerGenerated v.v_meta) config.Config.optimize config.Config.fusion (type_change_ok com v.v_type e.etype) (v.v_extra = None) b); *)
				b
			in
			let rec fuse acc el = match el with
				| ({eexpr = TVar(v1,None)} as e1) :: {eexpr = TBinop(OpAssign,{eexpr = TLocal v2},e2)} :: el when v1 == v2 ->
					changed := true;
					let e1 = {e1 with eexpr = TVar(v1,Some e2)} in
					change_num_writes v1 (-1);
					fuse (e1 :: acc) el
				| ({eexpr = TVar(v1,None)} as e1) :: ({eexpr = TIf(eif,_,Some _)} as e2) :: el when can_be_used_as_value com e2 && (match com.platform with Php -> false | Cpp when not (Common.defined com Define.Cppia) -> false | _ -> true) ->
					begin try
						let i = ref 0 in
						let check_assign e = match e.eexpr with
							| TBinop(OpAssign,{eexpr = TLocal v2},e2) when v1 == v2 -> incr i; e2
							| _ -> raise Exit
						in
						let e,_ = map_values ~allow_control_flow:false check_assign e2 in
						let e = match follow e.etype with
							| TAbstract({a_path=[],"Void"},_) -> {e with etype = v1.v_type}
							| _ -> e
						in
						let e1 = {e1 with eexpr = TVar(v1,Some e)} in
						changed := true;
						change_num_writes v1 (- !i);
						fuse (e1 :: acc) el
					with Exit ->
						fuse (e1 :: acc) (e2 :: el)
					end
				| ({eexpr = TVar(v1,Some e1)} as ev) :: e2 :: el when can_be_fused v1 e1 ->
					let found = ref false in
					let affected = ref false in
					let ik1 = get_interference_kind e1 in
					let check_interference e2 =
						let check ik e2 = match ik with
							| IKNone -> ()
							| IKSideEffect -> (* TODO: Could this miss a IKVarMod case? *)
								let rec loop e = match e.eexpr with
									| TMeta((Meta.Pure,_,_),_) ->
										()
									| TField _ when Optimizer.is_affected_type e.etype ->
										raise Exit
									| TCall({eexpr = TField(_,FStatic(c,cf))},el) when is_pure c cf ->
										List.iter loop el
									| TNew(c,_,el) when (match c.cl_constructor with Some cf when is_pure c cf -> true | _ -> false) ->
										List.iter loop el
									| TCall _ | TNew _ | TBinop((OpAssign | OpAssignOp _),_,_) | TUnop((Increment | Decrement),_,_) ->
										raise Exit
									| _ ->
										Type.iter loop e
								in
								loop e2
							| IKVarMod vl ->
								let rec loop e = match e.eexpr with
									| TLocal v when List.exists (fun v' -> v == v') vl -> raise Exit
									| _ -> Type.iter loop e
								in
								loop e2
						in
						try
							check ik1 e2;
							check (get_interference_kind e2) e1
						with Exit -> match com.platform with
							| Cpp when not (Common.defined com Define.Cppia) -> raise Exit
							| Php -> raise Exit (* They don't define evaluation order, so let's exit *)
							| _ -> affected := true;
					in
					let rec replace e =
						let e = match e.eexpr with
							| TWhile _ | TFunction _ ->
								e
							| TIf(e1,e2,eo) ->
								let e1 = replace e1 in
								{e with eexpr = TIf(e1,e2,eo)}
							| TSwitch(e1,cases,edef) ->
								let e1 = replace e1 in
								{e with eexpr = TSwitch(e1,cases,edef)}
							| TLocal v2 when v1 == v2 && not !affected ->
								found := true;
								e1
							| TBinop((OpAssign | OpAssignOp _ as op),({eexpr = TArray(e1,e2)} as ea),e3) ->
								let e1 = replace e1 in
								let e2 = replace e2 in
								let ea = {ea with eexpr = TArray(e1,e2)} in
								let e3 = replace e3 in
								{e with eexpr = TBinop(op,ea,e3)}
							| TBinop((OpAssign | OpAssignOp _ as op),e1,e2) ->
								let e2 = replace e2 in
								let e1 = match e1.eexpr with TLocal _ -> e1 | _ -> replace e1 in
								{e with eexpr = TBinop(op,e1,e2)}
							| TUnop((Increment | Decrement),_,{eexpr = TLocal _}) ->
								e
							| TCall({eexpr = TLocal v},_) when is_really_unbound v ->
								e
							| TCall(e1,el) when com.platform = Neko ->
								(* Neko has this reversed at the moment (issue #4787) *)
								let el = List.map replace el in
								let e1 = replace e1 in
								{e with eexpr = TCall(e1,el)}
							| _ ->
								Type.map_expr replace e
						in
						check_interference e;
						e
					in
					begin try
						let e = replace e2 in
						if not !found then raise Exit;
						changed := true;
						change_num_uses v1 (-1);
						fuse (e :: acc) el
					with Exit ->
						fuse (ev :: acc) (e2 :: el)
					end
				| {eexpr = TUnop((Increment | Decrement as op,Prefix,({eexpr = TLocal v} as ev)))} as e1 :: e2 :: el ->
					begin try
						let e2,f = match e2.eexpr with
							| TReturn (Some e2) -> e2,(fun e -> {e2 with eexpr = TReturn (Some e)})
							| TBinop(OpAssign,e21,e22) -> e22,(fun e -> {e2 with eexpr = TBinop(OpAssign,e21,e)})
							| TVar(v,Some e2) -> e2,(fun e -> {e2 with eexpr = TVar(v,Some e)})
							| _ -> raise Exit
						in
						let ops_match op1 op2 = match op1,op2 with
							| Increment,OpSub
							| Decrement,OpAdd ->
								true
							| _ ->
								false
						in
						begin match e2.eexpr with
							| TBinop(op2,{eexpr = TLocal v2},{eexpr = TConst (TInt i32)}) when v == v2 && Int32.to_int i32 = 1 && ops_match op op2 ->
								changed := true;
								change_num_uses v2 (-1);
								let e = (f {e1 with eexpr = TUnop(op,Postfix,ev)}) in
								fuse (e :: acc) el
							| TLocal v2 when v == v2 ->
								changed := true;
								change_num_uses v2 (-1);
								let e = (f {e1 with eexpr = TUnop(op,Prefix,ev)}) in
								fuse (e :: acc) el
							| _ ->
								raise Exit
						end
					with Exit ->
						fuse (e1 :: acc) (e2 :: el)
					end
				| e1 :: el ->
					fuse (e1 :: acc) el
				| [] ->
					acc
			in
			let rec loop e = match e.eexpr with
				| TBlock el ->
					let el = List.map loop el in
					(* fuse flips element order, but block_element doesn't care and flips it back *)
					let el = fuse [] el in
					let el = block_element [] el in
					let rec fuse_loop el =
						changed := false;
						let el = fuse [] el in
						let el = block_element [] el in
						if !changed then fuse_loop el else el
					in
					let el = fuse_loop el in
					{e with eexpr = TBlock el}
				| TCall({eexpr = TLocal v},_) when is_really_unbound v ->
					e
				| _ ->
					Type.map_expr loop e
			in
			let e = loop e in
			e
	end

	(*
		A BasicBlock represents a node in the control flow. It has expression elements similar to TBlock in the AST,
		but also holds additional information related to control flow and variables.

		Basic blocks are created whenever it is relevant for control flow. They differ from TBlock in that only their
		final element can be a control flow expression (the terminator). As a consequence, a given TBlock is split up
		into several basic blocks when control flow expressions are encountered.
	*)
	module BasicBlock = struct
		type block_kind =
			| BKRoot          (* The unique root block of the graph *)
			| BKNormal        (* A normal block *)
			| BKFunctionBegin (* Entry block of a function *)
			| BKFunctionEnd   (* Exit block of a function *)
			| BKSub           (* A sub block *)
			| BKConditional   (* A "then", "else" or "case" block *)
			| BKLoopHead      (* Header block of a loop *)
			| BKException     (* Relay block for exceptions *)
			| BKUnreachable   (* The unique unreachable block *)

		type cfg_edge_Flag =
			| FlagExecutable      (* Used by constant propagation to handle live edges *)
			| FlagDce             (* Used by DCE to keep track of handled edges *)
			| FlagCodeMotion      (* Used by code motion to track handled edges *)
			| FlagCopyPropagation (* Used by copy propagation to track handled eges *)

		type cfg_edge_kind =
			| CFGGoto                (* An unconditional branch *)
			| CFGFunction            (* Link to a function *)
			| CFGMaybeThrow          (* The block may or may not throw an exception *)
			| CFGCondBranch of texpr (* A conditional branch *)
			| CFGCondElse            (* A conditional alternative (else,default) *)

		and cfg_edge = {
			cfg_from : t;                           (* The source block *)
			cfg_to : t;                             (* The target block *)
			cfg_kind : cfg_edge_kind;               (* The edge kind *)
			mutable cfg_flags : cfg_edge_Flag list; (* Edge flags *)
		}

		and syntax_edge =
			| SEIfThen of t * t                                (* `if` with "then" and "next" *)
			| SEIfThenElse of t * t * t * Type.t               (* `if` with "then", "else" and "next" *)
			| SESwitch of (texpr list * t) list * t option * t (* `switch` with cases, "default" and "next" *)
			| SETry of t * (tvar * t) list * t                 (* `try` with catches and "next" *)
			| SEWhile of t * t                                 (* `while` with "body" and "next" *)
			| SESubBlock of t * t                              (* "sub" with "next" *)
			| SEMerge of t                                     (* Merge to same block *)
			| SEEnd                                            (* End of syntax *)
			| SENone                                           (* No syntax exit *)

		and t = {
			bb_id : int;                          (* The unique ID of the block *)
			bb_type : Type.t;                     (* The block type *)
			bb_pos : pos;                         (* The block position *)
			bb_kind : block_kind;                 (* The block kind *)
			mutable bb_closed : bool;             (* Whether or not the block has been closed *)
			(* elements *)
			bb_el : texpr DynArray.t;             (* The block expressions *)
			bb_phi : texpr DynArray.t;            (* SSA-phi expressions *)
			(* relations *)
			mutable bb_outgoing : cfg_edge list;  (* Outgoing edges *)
			mutable bb_incoming : cfg_edge list;  (* Incoming edges *)
			mutable bb_dominator : t;             (* The block's dominator *)
			mutable bb_dominated : t list;        (* The dominated blocks *)
			mutable bb_df : t list;               (* The dominance frontier *)
			mutable bb_syntax_edge : syntax_edge; (* The syntactic edge *)
			mutable bb_loop_groups : int list;    (* The loop groups this block belongs to *)
			mutable bb_scopes : int list;         (* The scopes this block belongs to *)
			(* variables *)
			mutable bb_var_writes : tvar list;    (* List of assigned variables *)
		}

		let s_block_kind = function
			| BKRoot -> "BKRoot"
			| BKNormal -> "BKNormal"
			| BKFunctionBegin -> "BKFunctionBegin"
			| BKFunctionEnd -> "BKFunctionEnd"
			| BKSub -> "BKSub"
			| BKConditional -> "BKConditional"
			| BKLoopHead -> "BKLoopHead"
			| BKException -> "BKException"
			| BKUnreachable -> "BKUnreachable"

		let s_cfg_edge_kind = function
			| CFGGoto -> "CFGGoto"
			| CFGFunction -> "CFGFunction"
			| CFGMaybeThrow -> "CFGMaybeThrow"
			| CFGCondBranch e -> "CFGCondBranch " ^ (s_expr_pretty e)
			| CFGCondElse -> "CFGCondElse"

		let has_flag edge flag =
			List.mem flag edge.cfg_flags

		let _create id kind scopes t p =
			let rec bb = {
				bb_kind = kind;
				bb_id = id;
				bb_type = t;
				bb_pos = p;
				bb_closed = false;
				bb_el = DynArray.create();
				bb_phi = DynArray.create();
				bb_outgoing = [];
				bb_incoming = [];
				bb_dominator = bb;
				bb_dominated = [];
				bb_df = [];
				bb_syntax_edge = SENone;
				bb_loop_groups = [];
				bb_var_writes = [];
				bb_scopes = scopes;
			} in
			bb

		let in_scope bb bb' = match bb'.bb_scopes with
			| [] -> error (Printf.sprintf "Scope-less block (kind: %s)" (s_block_kind bb'.bb_kind)) bb'.bb_pos
			| scope :: _ -> List.mem scope bb.bb_scopes
	end

	(*
		A Graph contains all relevant information for a given method. It is built from the field expression
		and then refined in subsequent modules such as Ssa.
	*)
	module Graph = struct
		open BasicBlock

		type texpr_lookup = BasicBlock.t * bool * int
		type tfunc_info = BasicBlock.t * Type.t * pos * tfunc
		type var_write = BasicBlock.t list
		type 'a itbl = (int,'a) Hashtbl.t

		type var_info = {
			vi_var : tvar;                            (* The variable itself *)
			vi_extra : tvar_extra;                    (* The original v_extra *)
			vi_bb_declare : BasicBlock.t;             (* The block where this variable was declared *)
			mutable vi_origin : tvar;                 (* The origin variable of this variable *)
			mutable vi_writes : var_write;            (* A list of blocks that assign to this variable *)
			mutable vi_value : texpr_lookup option;   (* The value of this variable, if known *)
			mutable vi_ssa_edges : texpr_lookup list; (* The expressions this variable influences *)
			mutable vi_reaching_def : tvar option;    (* The current reaching definition variable of this variable *)
		}

		type t = {
			mutable g_root : BasicBlock.t;             (* The unique root block *)
			mutable g_exit : BasicBlock.t;             (* The unique exit block *)
			mutable g_unreachable : BasicBlock.t;      (* The unique unreachable block *)
			mutable g_functions : tfunc_info itbl;     (* A map of functions, indexed by their block IDs *)
			mutable g_nodes : BasicBlock.t itbl;       (* A map of all blocks *)
			g_var_infos : var_info DynArray.t;         (* A map of variable information *)
			mutable g_loops : BasicBlock.t IntMap.t;   (* A map containing loop information *)
		}

		let create_var_info g bb v =
			let vi = {
				vi_var = v;
				vi_extra = v.v_extra;
				vi_bb_declare = bb;
				vi_origin = v;
				vi_writes = [];
				vi_value = None;
				vi_ssa_edges = [];
				vi_reaching_def = None;
			} in
			DynArray.add g.g_var_infos vi;
			let i = DynArray.length g.g_var_infos - 1 in
			v.v_extra <- Some([],Some (mk (TConst (TInt (Int32.of_int i))) t_dynamic null_pos))

		let get_var_info g v = match v.v_extra with
			| Some(_,Some {eexpr = TConst (TInt i32)}) -> DynArray.get g.g_var_infos (Int32.to_int i32)
			| _ -> assert false

		(* edges *)

		let set_syntax_edge g bb se =
			bb.bb_syntax_edge <- se

		let get_syntax_edge g bb =
			bb.bb_syntax_edge

		let add_cfg_edge g bb_from bb_to kind =
			if bb_from != g.g_unreachable then begin
				let edge = { cfg_from = bb_from; cfg_to = bb_to; cfg_kind = kind; cfg_flags = [] } in
				bb_from.bb_outgoing <- edge :: bb_from.bb_outgoing;
				bb_to.bb_incoming <- edge :: bb_to.bb_incoming;
			end

		let add_ssa_edge g v bb is_phi i =
			let vi = get_var_info g v in
			vi.vi_ssa_edges <- (bb,is_phi,i) :: vi.vi_ssa_edges

		(* nodes *)

		let add_function g tf t p bb =
			Hashtbl.add g.g_functions bb.bb_id (bb,t,p,tf)

		let alloc_id =
			let r = ref 1 in
			(fun () ->
				incr r;
				!r
			)

		let create_node g kind scopes t p =
			let bb = BasicBlock._create (alloc_id()) kind scopes t p in
			Hashtbl.add g.g_nodes bb.bb_id bb;
			bb

		let close_node g bb =
			if bb.bb_id > 0 then begin
				assert(not bb.bb_closed);
				bb.bb_closed <- true
			end

		let iter_dom_tree_from g bb f =
			let rec loop bb =
				f bb;
				List.iter loop bb.bb_dominated
			in
			loop bb

		let iter_dom_tree g f =
			iter_dom_tree_from g g.g_root f

		let iter_edges_from g bb f =
			iter_dom_tree_from g bb (fun bb -> List.iter f bb.bb_outgoing)

		let iter_edges g f =
			iter_dom_tree g (fun bb -> List.iter f bb.bb_outgoing)

		(* expressions *)

		let add_texpr g bb e =
			DynArray.add bb.bb_el e

		let get_texpr g bb is_phi i =
			DynArray.get (if is_phi then bb.bb_phi else bb.bb_el) i

		(* variables *)

		let declare_var g v bb =
			create_var_info g bb v

		let add_var_def g bb v =
			if bb.bb_id > 0 then begin
				bb.bb_var_writes <- v :: bb.bb_var_writes;
				let vi = get_var_info g v in
				vi.vi_writes <- bb :: vi.vi_writes;
			end

		let set_var_value g v bb is_phi i =
			(get_var_info g v).vi_value <- Some (bb,is_phi,i)

		let get_var_value g v =
			let value = (get_var_info g v).vi_value in
			let bb,is_phi,i = match value with
				| None -> raise Not_found
				| Some l -> l
			in
			match (get_texpr g bb is_phi i).eexpr with
			| TVar(_,Some e) | TBinop(OpAssign,_,e) -> e
			| _ -> assert false

		let add_var_origin g v v_origin =
			(get_var_info g v).vi_origin <- v_origin

		let get_var_origin g v =
			(get_var_info g v).vi_origin

		(* graph *)

		let create t p =
			let bb_root = BasicBlock._create 1 BKRoot [] t p; in
			let bb_unreachable = BasicBlock._create 0 BKUnreachable [] t_dynamic null_pos in
			let nodes = Hashtbl.create 0 in
			Hashtbl.add nodes bb_root.bb_id bb_root;
			{
				g_root = bb_root;
				g_exit = bb_unreachable;
				g_unreachable = bb_unreachable;
				g_functions = Hashtbl.create 0;
				g_nodes = nodes;
				g_var_infos = DynArray.create();
				g_loops = IntMap.empty;
			}

		let calculate_df g =
			iter_edges g (fun edge ->
				let rec loop bb =
					if bb != g.g_unreachable && bb != edge.cfg_to && bb != edge.cfg_to.bb_dominator then begin
						if edge.cfg_to != g.g_exit then bb.bb_df <- edge.cfg_to :: bb.bb_df;
						if bb.bb_dominator != bb then loop bb.bb_dominator
					end
				in
				loop edge.cfg_from
			)

		let check_integrity g =
			Hashtbl.iter (fun _ bb ->
				List.iter (fun edge ->
					if edge.cfg_to = g.g_unreachable then
						prerr_endline (Printf.sprintf "Outgoing edge from %i to the unreachable block" bb.bb_id)
					else if not (List.memq edge edge.cfg_to.bb_incoming) then
						prerr_endline (Printf.sprintf "Outgoing edge %i -> %i has no matching incoming edge" edge.cfg_from.bb_id edge.cfg_to.bb_id)
				) bb.bb_outgoing;
				List.iter (fun edge ->
					if edge.cfg_from == g.g_unreachable then
						prerr_endline (Printf.sprintf "Incoming edge to %i from the unreachable block" bb.bb_id)
					else if not (List.memq edge edge.cfg_from.bb_outgoing) then
						prerr_endline (Printf.sprintf "Incoming edge %i <- %i has no matching outgoing edge" edge.cfg_to.bb_id edge.cfg_from.bb_id)
				) bb.bb_incoming
			) g.g_nodes

		let calculate_immediate_dominators g =
			let semi = Hashtbl.create 0 in
			let semi_size = ref 0 in
			let parent = Hashtbl.create 0 in
			let bucket = Hashtbl.create 0 in
			let idom = Hashtbl.create 0 in
			let label = Hashtbl.create 0 in
			let ancestor = Hashtbl.create 0 in
			let nodes = DynArray.create () in
			let get_semi k = Hashtbl.find semi k in
			let set_semi k v = Hashtbl.replace semi k v in
			let get_parent k = Hashtbl.find parent k in
			let set_parent k v = Hashtbl.add parent k v in
			let get_label k = Hashtbl.find label k in
			let set_label k v = Hashtbl.replace label k v in
			let get_ancestor k = Hashtbl.find ancestor k in
			let set_ancestor k v = Hashtbl.replace ancestor k v in
			let has_ancestor k = Hashtbl.mem ancestor k in
			let get_idom k = Hashtbl.find idom k in
			let set_idom k v = Hashtbl.replace idom k v in
			let get_bucket k = try Hashtbl.find bucket k with Not_found -> [] in
			let add_to_bucket k v = Hashtbl.replace bucket k (v :: (get_bucket k)) in
			let clear_bucket k = Hashtbl.replace bucket k [] in
			let rec loop bb =
				bb.bb_dominated <- [];
				DynArray.add nodes bb;
				set_semi bb.bb_id !semi_size;
				incr semi_size;
				set_label bb.bb_id bb.bb_id;
				List.iter (fun edge ->
					let bb_to = edge.cfg_to in
					if not (Hashtbl.mem semi bb_to.bb_id) then begin
						set_parent bb_to.bb_id bb;
						loop bb_to
					end
				) bb.bb_outgoing
			in
			loop g.g_root;
			let compress v =
				let rec loop l a = try
					loop (a :: l) (Hashtbl.find ancestor a)
				with Not_found ->
					l
				in
				let worklist = loop [v] (get_ancestor v) in
				match worklist with
					| a :: worklist ->
						ignore(List.fold_left (fun (a,min_semi) desc ->
							let semi = get_semi (get_label desc) in
							if semi > min_semi then begin
								set_label desc (get_label a);
								(desc,min_semi)
							end else
								(desc,semi)
						) (a,get_semi (get_label a)) worklist)
					| [] ->
						assert false
			in
			let eval v =
				if has_ancestor v then begin
					compress v;
					get_label v;
				end else
					v
			in
			let link p c =
				set_ancestor c p
			in
			let rec loop nodes' = match nodes' with
				| [node] -> set_idom node.bb_id node.bb_id
				| [] -> assert false
				| w :: nodes' ->
					let p = get_parent w.bb_id in
					let semi = List.fold_left (fun acc v -> min acc (get_semi (eval v.cfg_from.bb_id))) (get_semi w.bb_id) w.bb_incoming in
					set_semi w.bb_id semi;
					add_to_bucket (DynArray.get nodes semi).bb_id w;
					link p.bb_id w.bb_id;
					List.iter (fun v ->
						let v = v.bb_id in
						let u = eval v in
						if get_semi u < get_semi v then
							set_idom v u
						else
							set_idom v p.bb_id
					) (get_bucket p.bb_id);
					clear_bucket p.bb_id;
					loop nodes'
			in
			loop (List.rev (DynArray.to_list nodes));
			List.iter (fun w ->
				let w = w.bb_id in
				let i = get_idom w in
				if i <> (DynArray.get nodes (get_semi w)).bb_id then
					set_idom w (get_idom i)
			) (List.tl ((DynArray.to_list nodes)));
			Hashtbl.iter (fun k v ->
				let bb = Hashtbl.find g.g_nodes k in
				let bb' = Hashtbl.find g.g_nodes v in
				bb.bb_dominator <- bb';
				if bb != bb' then bb'.bb_dominated <- bb :: bb'.bb_dominated
			) idom

		let finalize g bb_exit =
			calculate_immediate_dominators g;
			g.g_exit <- bb_exit
	end

	type analyzer_context = {
		com : Common.context;
		config : Config.t;
		graph : Graph.t;
		temp_var_name : string;
		is_real_function : bool;
		mutable entry : BasicBlock.t;
		mutable has_unbound : bool;
		mutable loop_counter : int;
		mutable loop_stack : int list;
		mutable scopes : int list;
		mutable scope_depth : int;
	}

	(*
		Transforms an expression to a graph, and a graph back to an expression. This module relies on TexprFilter being
		run first.

		The created graph is intact and can immediately be transformed back to an expression, or used for analysis first.
	*)
	module TexprTransformer = struct
		open BasicBlock
		open Graph

		let rec func ctx bb tf t p =
			let g = ctx.graph in
			let create_node kind t p =
				let bb = Graph.create_node g kind ctx.scopes t p in
				bb.bb_loop_groups <- ctx.loop_stack;
				bb
			in
			let bb_root = create_node BKFunctionBegin tf.tf_expr.etype tf.tf_expr.epos in
			let bb_exit = create_node BKFunctionEnd tf.tf_expr.etype tf.tf_expr.epos in
			List.iter (fun (v,_) ->
				declare_var g v bb_root;
				add_var_def g bb_root v
			) tf.tf_args;
			add_function g tf t p bb_root;
			add_cfg_edge g bb bb_root CFGFunction;
			let make_block_meta b =
				let e = mk (TConst (TInt (Int32.of_int b.bb_id))) ctx.com.basic.tint b.bb_pos in
				wrap_meta ":block" e
			in
			let bb_breaks = ref [] in
			let bb_continue = ref None in
			let b_try_stack = ref [] in
			let begin_loop bb_loop_pre bb_continue' =
				let old = !bb_breaks,!bb_continue in
				bb_breaks := [];
				bb_continue := Some bb_continue';
				let id = ctx.loop_counter in
				g.g_loops <- IntMap.add id bb_loop_pre g.g_loops;
				ctx.loop_stack <- id :: ctx.loop_stack;
				bb_continue'.bb_loop_groups <- id :: bb_continue'.bb_loop_groups;
				ctx.loop_counter <- id + 1;
				(fun () ->
					let breaks = !bb_breaks in
					bb_breaks := fst old;
					bb_continue := snd old;
					ctx.loop_stack <- List.tl ctx.loop_stack;
					breaks;
				)
			in
			let begin_try b =
				b_try_stack := b :: !b_try_stack;
				(fun () ->
					b_try_stack := List.tl !b_try_stack
				)
			in
			let increase_scope () =
				ctx.scope_depth <- ctx.scope_depth + 1;
				ctx.scopes <- ctx.scope_depth :: ctx.scopes;
				(fun () ->
					ctx.scopes <- List.tl ctx.scopes;
				)
			in
			let add_terminator bb e =
				add_texpr g bb e;
				close_node g bb;
				g.g_unreachable
			in
			let check_unbound_call v el =
				if is_unbound_call_that_might_have_side_effects v el then ctx.has_unbound <- true
			in
			let rec value bb e = match e.eexpr with
				| TLocal v ->
					bb,e
				| TBinop(OpAssign,({eexpr = TLocal v} as e1),e2) ->
					block_element bb e,e1
				| TBlock [e1] ->
					value bb e1
				| TBlock _ | TIf _ | TSwitch _ | TTry _ ->
					bind_to_temp bb false e
				| TCall({eexpr = TLocal v},el) when is_really_unbound v ->
					check_unbound_call v el;
					bb,e
				| TCall(e1,el) ->
					call bb e e1 el
				| TBinop((OpAssign | OpAssignOp _) as op,e1,e2) ->
					let bb,e2 = value bb e2 in
					let bb,e1 = value bb e1 in
					bb,{e with eexpr = TBinop(op,e1,e2)}
				| TBinop(op,e1,e2) ->
					let bb,e1,e2 = match ordered_value_list bb [e1;e2] with
						| bb,[e1;e2] -> bb,e1,e2
						| _ -> assert false
					in
					bb,{e with eexpr = TBinop(op,e1,e2)}
				| TUnop(op,flag,e1) ->
					let bb,e1 = value bb e1 in
					bb,{e with eexpr = TUnop(op,flag,e1)}
				| TArrayDecl el ->
					let bb,el = ordered_value_list bb el in
					bb,{e with eexpr = TArrayDecl el}
				| TObjectDecl fl ->
					let el = List.map snd fl in
					let bb,el = ordered_value_list bb el in
					bb,{e with eexpr = TObjectDecl (List.map2 (fun (s,_) e -> s,e) fl el)}
				| TField({eexpr = TTypeExpr _},fa) ->
					bb,e
				| TField(e1,fa) ->
					let bb,e1 = value bb e1 in
					bb,{e with eexpr = TField(e1,fa)}
				| TArray(e1,e2) ->
					let bb,e1,e2 = match ordered_value_list bb [e1;e2] with
						| bb,[e1;e2] -> bb,e1,e2
						| _ -> assert false
					in
					bb,{e with eexpr = TArray(e1,e2)}
				| TMeta(m,e1) ->
					let bb,e1 = value bb e1 in
					bb,{e with eexpr = TMeta(m,e1)}
				| TParenthesis e1 ->
					let bb,e1 = value bb e1 in
					bb,{e with eexpr = TParenthesis e1}
				| TCast(e1,mto) ->
					let bb,e1 = value bb e1 in
					bb,{e with eexpr = TCast(e1,mto)}
				| TNew(c,tl,el) ->
					let bb,el = ordered_value_list bb el in
					bb,{e with eexpr = TNew(c,tl,el)}
				| TEnumParameter(e1,ef,ei) ->
					let bb,e1 = value bb e1 in
					bb,{e with eexpr = TEnumParameter(e1,ef,ei)}
				| TFunction tf ->
					let bb_func,bb_func_end = func ctx bb tf e.etype e.epos in
					let e_fun = mk (TConst (TString "fun")) t_dynamic p in
					let econst = mk (TConst (TInt (Int32.of_int bb_func.bb_id))) ctx.com.basic.tint e.epos in
					let ec = mk (TCall(e_fun,[econst])) t_dynamic p in
					let bb_next = create_node BKNormal bb.bb_type bb.bb_pos in
					add_cfg_edge g bb bb_next CFGGoto;
					set_syntax_edge g bb (SEMerge bb_next);
					close_node g bb;
					add_cfg_edge g bb_func_end bb_next CFGGoto;
					bb_next,ec
				| TTypeExpr(TClassDecl {cl_kind = KAbstractImpl a}) when not (Meta.has Meta.RuntimeValue a.a_meta) ->
					error "Cannot use abstract as value" e.epos
				| TTypeExpr(TClassDecl c) ->
					List.iter (fun cf -> if not (Meta.has Meta.MaybeUsed cf.cf_meta) then cf.cf_meta <- (Meta.MaybeUsed,[],cf.cf_pos) :: cf.cf_meta;) c.cl_ordered_statics;
					bb,e
				| TConst _ | TTypeExpr _ ->
					bb,e
				| TThrow _ | TReturn _ | TBreak | TContinue ->
					let bb = block_element bb e in
					bb,mk (TConst TNull) t_dynamic e.epos
				| TVar _ | TFor _ | TWhile _ ->
					error "Cannot use this expression as value" e.epos
			and ordered_value_list bb el =
				let might_be_affected,collect_modified_locals = Optimizer.create_affection_checker() in
				let rec can_be_optimized e = match e.eexpr with
					| TBinop _ | TArray _ | TCall _ -> true
					| TParenthesis e1 -> can_be_optimized e1
					| _ -> false
				in
				let _,el = List.fold_left (fun (had_side_effect,acc) e ->
					if had_side_effect then
						(true,(might_be_affected e || Optimizer.has_side_effect e,can_be_optimized e,e) :: acc)
					else begin
						let had_side_effect = Optimizer.has_side_effect e in
						if had_side_effect then collect_modified_locals e;
						let opt = can_be_optimized e in
						(had_side_effect || opt,(false,opt,e) :: acc)
					end
				) (false,[]) (List.rev el) in
				let bb,values = List.fold_left (fun (bb,acc) (aff,opt,e) ->
					let bb,value = if aff || opt then bind_to_temp bb aff e else value bb e in
					bb,(value :: acc)
				) (bb,[]) el in
				bb,List.rev values
			and bind_to_temp bb sequential e =
				let rec loop fl e = match e.eexpr with
					| TField(e1,fa) when (match extract_field fa with Some {cf_kind = Method MethNormal} -> true | _ -> false) ->
						loop ((fun e' -> {e with eexpr = TField(e',fa)}) :: fl) e1
					| _ ->
						fl,e
				in
				let fl,e = loop [] e in
				let v = alloc_var ctx.temp_var_name e.etype in
				begin match ctx.com.platform with
					| Cpp when sequential && not (Common.defined ctx.com Define.Cppia) -> ()
					| _ -> v.v_meta <- [Meta.CompilerGenerated,[],e.epos];
				end;
				let bb = declare_var_and_assign bb v e in
				let e = {e with eexpr = TLocal v} in
				let e = List.fold_left (fun e f -> f e) e (List.rev fl) in
				bb,e
			and declare_var_and_assign bb v e =
				let rec loop bb e = match e.eexpr with
					| TParenthesis e1 ->
						loop bb e1
					| TBlock el ->
						let rec loop2 bb el = match el with
							| [e] ->
								bb,e
							| e1 :: el ->
								let bb = block_element bb e1 in
								loop2 bb el
							| [] ->
								assert false
						in
						let bb,e = loop2 bb el in
						loop bb e
					| _ ->
						bb,e
				in
				let bb,e = loop bb e in
				begin match follow v.v_type with
					| TAbstract({a_path=[],"Void"},_) -> error "Cannot use Void as value" e.epos
					| _ -> ()
				end;
				let ev = mk (TLocal v) v.v_type e.epos in
				let was_assigned = ref false in
				let assign e =
					if not !was_assigned then begin
						was_assigned := true;
						declare_var g v bb;
						add_texpr g bb (mk (TVar(v,None)) ctx.com.basic.tvoid ev.epos);
					end;
					mk (TBinop(OpAssign,ev,e)) ev.etype e.epos
				in
				begin try
					block_element_plus bb (map_values assign e) (fun e -> mk (TVar(v,Some e)) ctx.com.basic.tvoid e.epos)
				with Exit ->
					let bb,e = value bb e in
					declare_var g v bb;
					add_var_def g bb v;
					add_texpr g bb (mk (TVar(v,Some e)) ctx.com.basic.tvoid ev.epos);
					bb
				end
			and block_element_plus bb (e,efinal) f =
				let bb = block_element bb e in
				let bb = match efinal with
					| None -> bb
					| Some e -> block_element bb (f e)
				in
				bb
			and block_element_value bb e f =
				let e,efinal = map_values f e in
				block_element_plus bb (e,efinal) f
			and call bb e e1 el =
				begin match e1.eexpr with
					| TConst TSuper when ctx.com.platform = Java || ctx.com.platform = Cs ->
						bb,e
					| _ ->
						let check e t = match e.eexpr with
							| TLocal v when is_ref_type t ->
								v.v_capture <- true;
								e
							| _ ->
								e
						in
						let el = Codegen.UnificationCallback.check_call check el e1.etype in
						let bb,el = ordered_value_list bb (e1 :: el) in
						match el with
							| e1 :: el -> bb,{e with eexpr = TCall(e1,el)}
							| _ -> assert false
				end
			and block_element bb e = match e.eexpr with
				(* variables *)
				| TVar(v,None) ->
					declare_var g v bb;
					add_texpr g bb e;
					bb
				| TVar(v,Some e1) ->
					declare_var_and_assign bb v e1
				| TBinop(OpAssign,({eexpr = TLocal v} as e1),e2) ->
					let assign e =
						mk (TBinop(OpAssign,e1,e)) e.etype e.epos
					in
					begin try
						block_element_value bb e2 assign
					with Exit ->
						let bb,e2 = value bb e2 in
						add_var_def g bb v;
						add_texpr g bb {e with eexpr = TBinop(OpAssign,e1,e2)};
						bb
					end
				(* branching *)
				| TMeta((Meta.MergeBlock,_,_),{eexpr = TBlock el}) ->
					block_el bb el
				| TBlock el ->
					let scope = increase_scope() in
					let bb_sub = create_node BKSub e.etype e.epos in
					add_cfg_edge g bb bb_sub CFGGoto;
					close_node g bb;
					let bb_sub_next = block_el bb_sub el in
					scope();
					if bb_sub_next != g.g_unreachable then begin
						let bb_next = create_node BKNormal bb.bb_type bb.bb_pos in
						set_syntax_edge g bb (SESubBlock(bb_sub,bb_next));
						add_cfg_edge g bb_sub_next bb_next CFGGoto;
						close_node g bb_sub_next;
						bb_next;
					end else begin
						set_syntax_edge g bb (SEMerge bb_sub);
						close_node g bb_sub_next;
						bb_sub_next
					end
				| TIf(e1,e2,None) ->
					let bb,e1 = bind_to_temp bb false e1 in
					let scope = increase_scope() in
					let bb_then = create_node BKConditional e2.etype e2.epos in
					add_texpr g bb (wrap_meta ":cond-branch" e1);
					add_cfg_edge g bb bb_then (CFGCondBranch (mk (TConst (TBool true)) ctx.com.basic.tbool e2.epos));
					let bb_then_next = block bb_then e2 in
					scope();
					let bb_next = create_node BKNormal bb.bb_type bb.bb_pos in
					set_syntax_edge g bb (SEIfThen(bb_then,bb_next));
					add_cfg_edge g bb bb_next CFGCondElse;
					close_node g bb;
					add_cfg_edge g bb_then_next bb_next CFGGoto;
					close_node g bb_then_next;
					bb_next
				| TIf(e1,e2,Some e3) ->
					let bb,e1 = bind_to_temp bb false e1 in
					let scope = increase_scope() in
					let bb_then = create_node BKConditional e2.etype e2.epos in
					let bb_else = create_node BKConditional e3.etype e3.epos in
					add_texpr g bb (wrap_meta ":cond-branch" e1);
					add_cfg_edge g bb bb_then (CFGCondBranch (mk (TConst (TBool true)) ctx.com.basic.tbool e2.epos));
					add_cfg_edge g bb bb_else CFGCondElse;
					close_node g bb;
					let bb_then_next = block bb_then e2 in
					let bb_else_next = block bb_else e3 in
					scope();
					if bb_then_next == g.g_unreachable && bb_else_next == g.g_unreachable then begin
						set_syntax_edge g bb (SEIfThenElse(bb_then,bb_else,g.g_unreachable,e.etype));
						g.g_unreachable
					end else begin
						let bb_next = create_node BKNormal bb.bb_type bb.bb_pos in
						set_syntax_edge g bb (SEIfThenElse(bb_then,bb_else,bb_next,e.etype));
						add_cfg_edge g bb_then_next bb_next CFGGoto;
						add_cfg_edge g bb_else_next bb_next CFGGoto;
						close_node g bb_then_next;
						close_node g bb_else_next;
						bb_next
					end
				| TSwitch(e1,cases,edef) ->
					let is_exhaustive = edef <> None || Optimizer.is_exhaustive e1 in
					let bb,e1 = bind_to_temp bb false e1 in
					add_texpr g bb (wrap_meta ":cond-branch" e1);
					let reachable = ref [] in
					let make_case e =
						let scope = increase_scope() in
						let bb_case = create_node BKConditional e.etype e.epos in
						let bb_case_next = block bb_case e in
						scope();
						if bb_case_next != g.g_unreachable then
							reachable := bb_case_next :: !reachable;
						close_node g bb_case_next;
						bb_case
					in
					let cases = List.map (fun (el,e) ->
						let bb_case = make_case e in
						List.iter (fun e -> add_cfg_edge g bb bb_case (CFGCondBranch e)) el;
						el,bb_case
					) cases in
					let def = match edef with
						| None ->
							None
						| Some e ->
							let bb_case = make_case e in
							add_cfg_edge g bb bb_case (CFGCondElse);
							Some (bb_case)
					in
					if is_exhaustive && !reachable = [] then begin
						set_syntax_edge g bb (SESwitch(cases,def,g.g_unreachable));
						close_node g bb;
						g.g_unreachable;
					end else begin
						let bb_next = create_node BKNormal bb.bb_type bb.bb_pos in
						if not is_exhaustive then add_cfg_edge g bb bb_next CFGGoto;
						List.iter (fun bb -> add_cfg_edge g bb bb_next CFGGoto) !reachable;
						set_syntax_edge g bb (SESwitch(cases,def,bb_next));
						close_node g bb;
						bb_next
					end
				| TWhile(e1,e2,NormalWhile) ->
					let bb_loop_pre = create_node BKNormal e1.etype e1.epos in
					add_cfg_edge g bb bb_loop_pre CFGGoto;
					set_syntax_edge g bb (SEMerge bb_loop_pre);
					close_node g bb;
					let bb_loop_head = create_node BKLoopHead e1.etype e1.epos in
					add_cfg_edge g bb_loop_pre bb_loop_head CFGGoto;
					let scope = increase_scope() in
					let close = begin_loop bb bb_loop_head in
					let bb_loop_body = create_node BKNormal e2.etype e2.epos in
					let bb_loop_body_next = block bb_loop_body e2 in
					let bb_breaks = close() in
					scope();
					let dom = match bb_breaks with
						| [] ->
							add_cfg_edge g bb_loop_body_next bb_exit CFGGoto;
							g.g_unreachable
						| [bb_break] -> bb_break
						| _ -> bb_loop_body (* TODO: this is not accurate for while(true) loops *)
					in
					let bb_next = if dom == g.g_unreachable then g.g_unreachable else create_node BKNormal bb.bb_type bb.bb_pos in
					List.iter (fun bb -> add_cfg_edge g bb bb_next CFGGoto) bb_breaks;
					set_syntax_edge g bb_loop_pre (SEWhile(bb_loop_body,bb_next));
					close_node g bb_loop_pre;
					add_texpr g bb_loop_pre {e with eexpr = TWhile(e1,make_block_meta bb_loop_body,NormalWhile)};
					add_cfg_edge g bb_loop_body_next bb_loop_head CFGGoto;
					add_cfg_edge g bb_loop_head bb_loop_body CFGGoto;
					close_node g bb_loop_body_next;
					close_node g bb_loop_head;
					bb_next;
				| TTry(e1,catches) ->
					let scope = increase_scope() in
					let bb_try = create_node BKNormal e1.etype e1.epos in
					let bb_exc = create_node BKException t_dynamic e.epos in
					add_cfg_edge g bb bb_try CFGGoto;
					let close = begin_try bb_exc in
					let bb_try_next = block bb_try e1 in
					close();
					scope();
					let bb_next = if bb_exc.bb_incoming = [] then
						let bb_next = if bb_try_next == g.g_unreachable then
							g.g_unreachable
						else begin
							let bb_next = create_node BKNormal bb.bb_type bb.bb_pos in
							add_cfg_edge g bb_try_next bb_next CFGGoto;
							close_node g bb_try_next;
							bb_next
						end in
						set_syntax_edge g bb (SESubBlock(bb_try,bb_next));
						bb_next
					else begin
						let is_reachable = ref (not (bb_try_next == g.g_unreachable)) in
						let catches = List.map (fun (v,e) ->
							let scope = increase_scope() in
							let bb_catch = create_node BKNormal e.etype e.epos in
							declare_var ctx.graph v bb_catch;
							add_var_def g bb_catch v;
							add_cfg_edge g bb_exc bb_catch CFGGoto;
							let bb_catch_next = block bb_catch e in
							scope();
							is_reachable := !is_reachable || (not (bb_catch_next == g.g_unreachable));
							v,bb_catch,bb_catch_next
						) catches in
						let bb_next = if !is_reachable then create_node BKNormal bb.bb_type bb.bb_pos else g.g_unreachable in
						let catches = List.map (fun (v,bb_catch,bb_catch_next) ->
							if bb_catch_next != g.g_unreachable then add_cfg_edge g bb_catch_next bb_next CFGGoto;
							close_node g bb_catch_next;
							v,bb_catch
						) catches in
						set_syntax_edge g bb (SETry(bb_try,catches,bb_next));
						if bb_try_next != g.g_unreachable then add_cfg_edge g bb_try_next bb_next CFGGoto;
						close_node g bb_try_next;
						bb_next
					end in
					close_node g bb_exc;
					close_node g bb;
					bb_next
				(* control flow *)
				| TReturn None ->
					add_cfg_edge g bb bb_exit CFGGoto;
					add_terminator bb e
				| TReturn (Some e1) ->
					begin try
						let mk_return e1 = mk (TReturn (Some e1)) t_dynamic e.epos in
						block_element_value bb e1 mk_return
					with Exit ->
						let bb,e1 = value bb e1 in
						add_cfg_edge g bb bb_exit CFGGoto;
						add_terminator bb {e with eexpr = TReturn(Some e1)};
					end
				| TBreak ->
					bb_breaks := bb :: !bb_breaks;
					add_terminator bb e
				| TContinue ->
					begin match !bb_continue with
						| Some bb_continue -> add_cfg_edge g bb bb_continue CFGGoto
						| _ -> assert false
					end;
					add_terminator bb e
				| TThrow e1 ->
					begin try
						let mk_throw e1 = mk (TThrow e1) t_dynamic e.epos in
						block_element_value bb e1 mk_throw
					with Exit ->
						let bb,e1 = value bb e1 in
						begin match !b_try_stack with
							| [] -> add_cfg_edge g bb bb_exit CFGGoto
							| _ -> List.iter (fun bb_exc -> add_cfg_edge g bb bb_exc CFGGoto) !b_try_stack;
						end;
						add_terminator bb {e with eexpr = TThrow e1};
					end
				(* side_effects *)
				| TCall({eexpr = TLocal v},el) when is_really_unbound v ->
					check_unbound_call v el;
					add_texpr g bb e;
					bb
				| TCall(e1,el) ->
					let bb,e = call bb e e1 el in
					add_texpr g bb e;
					bb
				| TNew(c,tl,el) ->
					let bb,el = ordered_value_list bb el in
					add_texpr g bb {e with eexpr = TNew(c,tl,el)};
					bb
				| TCast(e1,Some mt) ->
					let b,e1 = value bb e1 in
					add_texpr g bb {e with eexpr = TCast(e1,Some mt)};
					bb
				| TBinop((OpAssign | OpAssignOp _) as op,({eexpr = TArray(e1,e2)} as ea),e3) ->
					let bb,e1,e2,e3 = match ordered_value_list bb [e1;e2;e3] with
						| bb,[e1;e2;e3] -> bb,e1,e2,e3
						| _ -> assert false
					in
					add_texpr g bb {e with eexpr = TBinop(op,{ea with eexpr = TArray(e1,e2)},e3)};
					bb
				| TBinop((OpAssign | OpAssignOp _ as op),e1,e2) ->
					let bb,e1 = value bb e1 in
					let bb,e2 = value bb e2 in
					add_texpr g bb {e with eexpr = TBinop(op,e1,e2)};
					bb
				| TUnop((Increment | Decrement as op),flag,e1) ->
					let bb,e1 = value bb e1 in
					add_texpr g bb {e with eexpr = TUnop(op,flag,e1)};
					bb
				| TLocal _ when not ctx.config.Config.local_dce ->
					add_texpr g bb e;
					bb
				(* no-side-effect *)
				| TEnumParameter _ | TFunction _ | TConst _ | TTypeExpr _ | TLocal _ ->
					bb
				(* no-side-effect composites *)
				| TParenthesis e1 | TMeta(_,e1) | TCast(e1,None) | TField(e1,_) | TUnop(_,_,e1) ->
					block_element bb e1
				| TArray(e1,e2) | TBinop(_,e1,e2) ->
					let bb = block_element bb e1 in
					block_element bb e2
				| TArrayDecl el ->
					block_el bb el
				| TObjectDecl fl ->
					block_el bb (List.map snd fl)
				| TFor _ | TWhile(_,_,DoWhile) ->
					assert false
			and block_el bb el =
				match !b_try_stack with
				| [] ->
					let rec loop bb el = match el with
						| [] -> bb
						| e :: el ->
							let bb = block_element bb e in
							if bb == g.g_unreachable then bb else loop bb el
					in
					loop bb el
				| bbl ->
					let rec loop bb el = match el with
						| [] -> bb
						| e :: el ->
							let bb = if not (can_throw e) then
								block_element bb e
							else begin
								let bb' = create_node BKNormal e.etype e.epos in
								add_cfg_edge g bb bb' CFGGoto;
								List.iter (fun bb_exc -> add_cfg_edge g bb bb_exc CFGMaybeThrow) bbl;
								set_syntax_edge g bb (SEMerge bb');
								close_node g bb;
								block_element bb' e
							end in
							if bb == g.g_unreachable then bb else loop bb el
					in
					loop bb el
			and block bb e =
				let el = match e.eexpr with
					| TBlock el -> el
					| _ -> [e]
				in
				block_el bb el
			in
			let bb_last = block bb_root tf.tf_expr in
			close_node g bb_last;
			add_cfg_edge g bb_last bb_exit CFGGoto; (* implied return *)
			close_node g bb_exit;
			bb_root,bb_exit

		let from_texpr com config e =
			let g = Graph.create e.etype e.epos in
			let tf,is_real_function = match e.eexpr with
				| TFunction tf ->
					tf,true
				| _ ->
					(* Wrap expression in a function so we don't have to treat it as a special case throughout. *)
					let e = mk (TReturn (Some e)) t_dynamic e.epos in
					let tf = { tf_args = []; tf_type = e.etype; tf_expr = e; } in
					tf,false
			in
			let ctx = {
				com = com;
				config = config;
				graph = g;
				(* For CPP we want to use variable names which are "probably" not used by users in order to
				   avoid problems with the debugger, see https://github.com/HaxeFoundation/hxcpp/issues/365 *)
				temp_var_name = (match com.platform with Cpp -> "_hx_tmp" | _ -> "tmp");
				is_real_function = is_real_function;
				entry = g.g_unreachable;
				has_unbound = false;
				loop_counter = 0;
				loop_stack = [];
				scope_depth = 0;
				scopes = [0];
			} in
			let bb_func,bb_exit = func ctx g.g_root tf e.etype e.epos in
			ctx.entry <- bb_func;
			close_node g g.g_root;
			finalize g bb_exit;
			set_syntax_edge g bb_exit SEEnd;
			ctx

		let rec block_to_texpr_el ctx bb =
			if bb.bb_dominator == ctx.graph.g_unreachable then
				[]
			else begin
				let block bb = block_to_texpr ctx bb in
				let rec loop bb se =
					let el = List.rev (DynArray.to_list bb.bb_el) in
					match el,se with
					| el,SESubBlock(bb_sub,bb_next) ->
						Some bb_next,(block bb_sub) :: el
					| el,SEMerge bb_next ->
						Some bb_next,el
					| el,(SEEnd | SENone) ->
						None,el
					| {eexpr = TWhile(e1,_,flag)} as e :: el,(SEWhile(bb_body,bb_next)) ->
						let e2 = block bb_body in
						Some bb_next,{e with eexpr = TWhile(e1,e2,flag)} :: el
					| el,SETry(bb_try,bbl,bb_next) ->
						Some bb_next,(mk (TTry(block bb_try,List.map (fun (v,bb) -> v,block bb) bbl)) ctx.com.basic.tvoid bb_try.bb_pos) :: el
					| e1 :: el,se ->
						let e1 = Texpr.skip e1 in
						let bb_next,e1_def,t = match se with
							| SEIfThen(bb_then,bb_next) -> Some bb_next,TIf(e1,block bb_then,None),ctx.com.basic.tvoid
							| SEIfThenElse(bb_then,bb_else,bb_next,t) -> Some bb_next,TIf(e1,block bb_then,Some (block bb_else)),t
							| SESwitch(bbl,bo,bb_next) -> Some bb_next,TSwitch(e1,List.map (fun (el,bb) -> el,block bb) bbl,Option.map block bo),ctx.com.basic.tvoid
							| _ -> error (Printf.sprintf "Invalid node exit: %s" (s_expr_pretty e1)) bb.bb_pos
						in
						bb_next,(mk e1_def t e1.epos) :: el
					| [],_ ->
						None,[]
				in
				let bb_next,el = loop bb bb.bb_syntax_edge in
				let el = match bb_next with
					| None -> el
					| Some bb -> (block_to_texpr_el ctx bb) @ el
				in
				el
			end

		and block_to_texpr ctx bb =
			assert(bb.bb_closed);
			let el = block_to_texpr_el ctx bb in
			let e = mk (TBlock (List.rev el)) bb.bb_type bb.bb_pos in
			e

		and func ctx i =
			let bb,t,p,tf = Hashtbl.find ctx.graph.g_functions i in
			let e = block_to_texpr ctx bb in
			let rec loop e = match e.eexpr with
				| TLocal v when not (is_unbound v) ->
					{e with eexpr = TLocal (get_var_origin ctx.graph v)}
				| TVar(v,eo) when not (is_unbound v) ->
					let eo = Option.map loop eo in
					let v' = get_var_origin ctx.graph v in
					{e with eexpr = TVar(v',eo)}
				| TBinop(OpAssign,e1,({eexpr = TBinop(op,e2,e3)} as e4)) ->
					let e1 = loop e1 in
					let e2 = loop e2 in
					let e3 = loop e3 in
					let is_valid_assign_op = function
						| OpAdd | OpMult | OpDiv | OpSub | OpAnd
						| OpOr | OpXor | OpShl | OpShr | OpUShr | OpMod ->
							true
						| OpAssignOp _ | OpInterval | OpArrow | OpAssign | OpEq
						| OpNotEq | OpGt | OpGte | OpLt | OpLte | OpBoolAnd | OpBoolOr ->
							false
					in
					begin match e1.eexpr,e2.eexpr with
						| TLocal v1,TLocal v2 when v1 == v2 && is_valid_assign_op op ->
							begin match op,e3.eexpr with
								| OpAdd,TConst (TInt i32) when Int32.to_int i32 = 1 -> {e with eexpr = TUnop(Increment,Prefix,e1)}
								| OpSub,TConst (TInt i32) when Int32.to_int i32 = 1 -> {e with eexpr = TUnop(Decrement,Prefix,e1)}
								| _ -> {e with eexpr = TBinop(OpAssignOp op,e1,e3)}
							end
						| _ ->
							{e with eexpr = TBinop(OpAssign,e1,{e4 with eexpr = TBinop(op,e2,e3)})}
					end
				| TCall({eexpr = TConst (TString "fun")},[{eexpr = TConst (TInt i32)}]) ->
					func ctx (Int32.to_int i32)
				| TCall({eexpr = TLocal v},_) when is_really_unbound v ->
					e
				| _ ->
					Type.map_expr loop e
			in
			let e = loop e in
			mk (TFunction {tf with tf_expr = e}) t p

		let to_texpr ctx =
			func ctx ctx.entry.bb_id
	end

	(*
		Ssa changes the expressions of a graph to conform to SSA rules. All variables are assigned to only once
		and SSA-phi expressions are created where necessary.

		The first pass inserts SSA-phi expressions for each variable in the dominance frontier of all its defining
		blocks.

		The second pass then creates and renames variables to ensure SSA property.
	*)
	module Ssa = struct
		open BasicBlock
		open Graph

		let add_phi g bb v =
			let p = bb.bb_pos in
			let ev = mk (TLocal v) v.v_type p in
			let el = List.map (fun _ -> ev) bb.bb_incoming in
			let e_phi = mk (TConst (TString "phi")) t_dynamic p in
			let ec = mk (TCall(e_phi,el)) t_dynamic p in
			let e = mk (TBinop(OpAssign,ev,ec)) t_dynamic p in
			DynArray.add bb.bb_phi e

		let insert_phi ctx =
			DynArray.iter (fun vi ->
				let v = vi.vi_var in
				if vi.vi_bb_declare == ctx.graph.g_unreachable then
					()
				else begin
					let done_list = Hashtbl.create 0 in
					let w = ref vi.vi_writes in
					while !w <> [] do
						let x = List.hd !w in
						w := List.tl !w;
						List.iter (fun y ->
							if not (Hashtbl.mem done_list y.bb_id) then begin
								Hashtbl.add done_list y.bb_id true;
								if in_scope y vi.vi_bb_declare then begin
									add_phi ctx.graph y v;
									if not (List.memq y vi.vi_writes) then
										w := y :: !w
								end
							end
						) x.bb_df;
					done
				end
			) ctx.graph.g_var_infos

		let set_reaching_def g v vo =
			let vi = get_var_info g v in
			vi.vi_reaching_def <- vo

		let get_reaching_def g v =
			(get_var_info g v).vi_reaching_def

		let rec dominates bb_dom bb =
			bb_dom == bb || bb.bb_dominator == bb_dom || (bb.bb_dominator != bb && dominates bb_dom bb.bb_dominator)

		let dominates ctx r bb =
			let l = (get_var_info ctx.graph r).vi_writes in
			List.exists (fun bb' -> dominates bb' bb) l

		let update_reaching_def ctx v bb =
			let rec loop r = match r with
				| Some r ->
					if dominates ctx r bb then
						Some r
					else
						loop (get_reaching_def ctx.graph r)
				| None ->
					None
			in
			let v' = (loop (get_reaching_def ctx.graph v)) in
			set_reaching_def ctx.graph v v'

		let local ctx e v bb =
			update_reaching_def ctx v bb;
			match get_reaching_def ctx.graph v with
				| Some v' -> v'
				| None -> v

		let update_phi ctx edge =
			let bb = edge.cfg_to in
			let rec loop i e =
				match e.eexpr with
				| TBinop(OpAssign,({eexpr = TLocal v0} as e1), ({eexpr = TCall({eexpr = TConst (TString "phi")} as ephi,el)} as ecall)) ->
					let el = List.map2 (fun e inc ->
						let bb_pred = inc.cfg_from in
						if bb_pred != edge.cfg_from then
							e
						else match e.eexpr with
						| TLocal v ->
							let v' = local ctx e v edge.cfg_from in
							add_ssa_edge ctx.graph v' bb true i;
							{e with eexpr = TLocal v'}
						| _ ->
							assert false
					) el edge.cfg_to.bb_incoming in
					let ephi = {ecall with eexpr = TCall(ephi,el)} in
					set_var_value ctx.graph v0 bb true i;
					{e with eexpr = TBinop(OpAssign,e1,ephi)}
				| _ ->
					Type.map_expr (loop i) e
			in
			dynarray_mapi loop bb.bb_phi

		let rec rename_in_block ctx bb =
			let write_var v is_phi i =
				update_reaching_def ctx v bb;
				let v' = alloc_var (v.v_name) v.v_type in
				declare_var ctx.graph v' bb;
				v'.v_meta <- v.v_meta;
				v'.v_capture <- v.v_capture;
				add_var_def ctx.graph bb v';
				set_reaching_def ctx.graph v' (get_reaching_def ctx.graph v);
				set_reaching_def ctx.graph v (Some v');
				set_var_value ctx.graph v' bb is_phi i;
				add_var_origin ctx.graph v' v;
				v'
			in
			let rec loop is_phi i e = match e.eexpr with
				| TLocal v when not (is_unbound v) ->
					let v' = local ctx e v bb in
					add_ssa_edge ctx.graph v' bb is_phi i;
					{e with eexpr = TLocal v'}
				| TVar(v,Some e1) when not (is_unbound v) ->
					let e1 = (loop is_phi i) e1 in
					let v' = write_var v is_phi i in
					{e with eexpr = TVar(v',Some e1)}
				| TBinop(OpAssign,({eexpr = TLocal v} as e1),e2) when not (is_unbound v) ->
					let e2 = (loop is_phi i) e2 in
					let v' = write_var v is_phi i in
					{e with eexpr = TBinop(OpAssign,{e1 with eexpr = TLocal v'},e2)};
				| TCall({eexpr = TConst (TString "phi")},_) ->
					e
				| _ ->
					Type.map_expr (loop is_phi i) e
			in
			dynarray_mapi (loop true) bb.bb_phi;
			dynarray_mapi (loop false) bb.bb_el;
			List.iter (update_phi ctx) bb.bb_outgoing;
			List.iter (rename_in_block ctx) bb.bb_dominated

		let apply ctx =
			Graph.calculate_df ctx.graph;
			insert_phi ctx;
			rename_in_block ctx ctx.graph.g_root
	end

	module type DataFlowApi = sig
		type t
		val flag : BasicBlock.cfg_edge_Flag
		val transfer : analyzer_context -> BasicBlock.t -> texpr -> t (* The transfer function *)
		val equals : t -> t -> bool                                   (* The equality function *)
		val bottom : t                                                (* The bottom element of the lattice *)
		val top : t                                                   (* The top element of the lattice *)
		val get_cell : int -> t                                       (* Lattice cell getter *)
		val set_cell : int -> t -> unit                               (* Lattice cell setter *)
		val init : analyzer_context -> unit                           (* The initialization function which is called at the start *)
		val commit : analyzer_context -> unit                         (* The commit function which is called at the end *)
		val conditional : bool                                        (* Whether or not conditional branches are checked *)
	end

	(*
		DataFlow provides a framework for data flow analysis. It follows CFG edges from the root of the graph
		and visits the expressions and SSA-phi expressions of blocks on its way.

		If such an expression assigns to a variable (TVar or TBinop(OpAsssign)), all uses of that variable are
		checked by following the variable's SSA edges.

		A conditional branch edge (CFGCondBranch and CFGCondElse) is only followed if the available information
		suggests that it might be executable. This causes information from dead branches to not be taken into
		account.

		For SSA-phi nodes, only those incoming edges which are considered to be executable are processed.

		The algorithm continues until no further changes occur.
	*)
	module DataFlow (M : DataFlowApi) = struct
		open Graph
		open BasicBlock

		let get_ssa_edges_from g v =
			(get_var_info g v).vi_ssa_edges

		let run ctx =
			let g = ctx.graph in
			let ssa_work_list = ref [] in
			let cfg_work_list = ref g.g_root.bb_outgoing in
			let add_ssa_edge edge =
				ssa_work_list := edge :: !ssa_work_list
			in
			let add_cfg_edge edge =
				cfg_work_list := edge :: !cfg_work_list
			in
			let visit_phi bb v el =
				let el = List.fold_left2 (fun acc e edge ->
					if has_flag edge M.flag then e :: acc else acc
				) [] el bb.bb_incoming in
				let el = List.map (fun e -> M.transfer ctx bb e) el in
				match el with
					| e1 :: el when List.for_all (M.equals e1) el ->
						e1;
					| _ ->
						M.bottom;
			in
			let set_lattice_cell v e =
				let e' = M.get_cell v.v_id in
				M.set_cell v.v_id e;
				if not (M.equals e e') then
					List.iter (fun edge -> add_ssa_edge edge) (get_ssa_edges_from g v);
			in
			let visit_assignment bb v e =
				match e.eexpr with
				| TCall({eexpr = TConst (TString "phi")},el) ->
					set_lattice_cell v (visit_phi bb v el)
				| _ ->
					if List.exists (fun edge -> has_flag edge M.flag) bb.bb_incoming then
						set_lattice_cell v (M.transfer ctx bb e)
			in
			let visit_expression bb e =
				match e.eexpr with
				| TBinop(OpAssign,{eexpr = TLocal v},e2) | TVar(v,Some e2) ->
					visit_assignment bb v e2;
					false
				| TMeta((Meta.Custom ":cond-branch",_,_),e1) when M.conditional ->
					let e1 = M.transfer ctx bb e1 in
					let edges = if e1 == M.bottom || e1 == M.top then
						bb.bb_outgoing
					else begin
						let rec loop yes maybe also edges = match edges with
							| edge :: edges ->
								begin match edge.cfg_kind with
								| CFGCondBranch e ->
									let e = M.transfer ctx bb e in
									if M.equals e e1 then
										loop (edge :: yes) maybe also edges
									else
										loop yes maybe also edges
								| CFGCondElse ->
									loop yes (edge :: maybe) also edges
								| CFGGoto | CFGFunction | CFGMaybeThrow ->
									loop yes maybe (edge :: also) edges
								end
							| [] ->
								yes,maybe,also
						in
						let yes,maybe,also = loop [] [] [] bb.bb_outgoing in
						match yes,maybe with
							| [],[] -> bb.bb_outgoing
							| [],maybe -> maybe @ also
							| yes,_ -> yes @ also
					end in
					List.iter add_cfg_edge edges;
					true
				| _ ->
					false
			in
			let visit_expressions bb =
				let b = DynArray.fold_left (fun b e ->
					visit_expression bb e || b
				) false bb.bb_el in
				if not b then List.iter add_cfg_edge bb.bb_outgoing
			in
			let visit_phis bb =
				DynArray.iter (fun e ->
					match e.eexpr with
						| TBinop(OpAssign,{eexpr = TLocal v},{eexpr = TCall({eexpr = TConst (TString "phi")},el)}) ->
							set_lattice_cell v (visit_phi bb v el)
						| _ -> assert false
				) bb.bb_phi
			in
			let rec loop () = match !cfg_work_list,!ssa_work_list with
				| edge :: edges,_ ->
					cfg_work_list := edges;
					if not (has_flag edge M.flag) then begin
						edge.cfg_flags <- M.flag :: edge.cfg_flags;
						visit_phis edge.cfg_to;
						let i = List.fold_left (fun i edge -> i + if has_flag edge M.flag then 1 else 0) 0 edge.cfg_to.bb_incoming in
						if i = 1 || edge.cfg_to == g.g_root then
							visit_expressions edge.cfg_to;
						begin match edge.cfg_to.bb_outgoing with
							| [edge] -> add_cfg_edge edge
							| _ -> ()
						end
					end;
					loop();
				| [],((bb,is_phi,i) :: edges) ->
					ssa_work_list := edges;
					let e = get_texpr g bb is_phi i in
					ignore(visit_expression bb e);
					loop()
				| [],[] ->
					()
			in
			loop ()

		let apply ctx =
			M.init ctx;
			run ctx;
			M.commit ctx
	end

	(*
		ConstPropagation implements sparse conditional constant propagation using the DataFlow algorithm. Its lattice consists of
		constants and enum values, but only the former are propagated. Enum values are treated as immutable data tuples and allow
		extracting constants, their index or other enum values.

		This module also deals with binop/unop optimization and standard API inlining.
	*)
	module ConstPropagation = DataFlow(struct
		open BasicBlock

		type t =
			| Top
			| Bottom
			| Const of tconstant
			| EnumValue of int * t list

		let conditional = true
		let flag = FlagExecutable

		let lattice = Hashtbl.create 0

		let get_cell i = try Hashtbl.find lattice i with Not_found -> Top
		let set_cell i ct = Hashtbl.replace lattice i ct

		let top = Top
		let bottom = Bottom

		let equals lat1 lat2 = match lat1,lat2 with
			| Top,Top | Bottom,Bottom -> true
			| Const ct1,Const ct2 -> ct1 = ct2
			| EnumValue(i1,_),EnumValue(i2,_) -> i1 = i2
			| _ -> false

		let transfer ctx bb e =
			let rec eval bb e =
				let wrap = function
					| Const ct -> mk (TConst ct) t_dynamic null_pos
					| _ -> raise Exit
				in
				let unwrap e = match e.eexpr with
					| TConst ct -> Const ct
					| _ -> raise Exit
				in
				match e.eexpr with
				| TConst (TSuper | TThis | TNull) ->
					Bottom
				| TConst ct ->
					Const ct
				| TLocal v ->
					if is_unbound v || (follow v.v_type) == t_dynamic || v.v_capture then
						Bottom
					else
						get_cell v.v_id
				| TBinop(OpAssign,_,e2) ->
					eval bb e2
				| TBinop(op,e1,e2) ->
					let cl1 = eval bb e1 in
					let cl2 = eval bb e2 in
					let e1 = wrap cl1 in
					let e2 = wrap cl2 in
					let e = {e with eexpr = TBinop(op,e1,e2)} in
					let e' = Optimizer.optimize_binop e op e1 e2 in
					if e != e' then
						eval bb e'
					else
						unwrap e'
				| TUnop(op,flag,e1) ->
					let cl1 = eval bb e1 in
					let e1 = wrap cl1 in
					let e = {e with eexpr = TUnop(op,flag,e1)} in
					let e' = Optimizer.optimize_unop e op flag e1 in
					if e != e' then
						eval bb e'
					else
						unwrap e'
				| TField(_,FEnum(_,ef)) ->
					EnumValue(ef.ef_index,[])
				| TCall({eexpr = TField(_,FEnum(_,ef))},el) ->
					let cll = List.map (fun e -> try eval bb e with Exit -> Bottom) el in
					EnumValue(ef.ef_index,cll)
				| TEnumParameter(e1,_,i) ->
					begin match eval bb e1 with
						| EnumValue(_,el) -> (try List.nth el i with Failure _ -> raise Exit)
						| _ -> raise Exit
					end;
				| TCall ({ eexpr = TField (_,FStatic(c,cf))},el) ->
					let el = List.map (eval bb) el in
					let el = List.map wrap el in
					begin match Optimizer.api_inline2 ctx.com c cf.cf_name el e.epos with
						| None -> raise Exit
						| Some e -> eval bb e
					end
				| TParenthesis e1 | TMeta(_,e1) | TCast(e1,None) ->
					eval bb e1
				| _ ->
					let e1 = match ctx.com.platform,e.eexpr with
						| Js,TArray(e1,{eexpr = TConst(TInt i)}) when Int32.to_int i = 1 -> e1
						| Cpp,TCall({eexpr = TField(e1,FDynamic "__Index")},[]) -> e1
						| Neko,TField(e1,FDynamic "index") -> e1
						| _ -> raise Exit
					in
					begin match follow e1.etype,eval bb e1 with
						| TEnum _,EnumValue(i,_) -> Const (TInt (Int32.of_int i))
						| _ -> raise Exit
					end
			in
			try
				eval bb e
			with Exit ->
				Bottom

		let init ctx =
			Hashtbl.clear lattice

		let commit ctx =
			let inline e i = match get_cell i with
				| Top | Bottom | EnumValue _ ->
					raise Not_found
				| Const ct ->
					let e' = Codegen.type_constant ctx.com (tconst_to_const ct) e.epos in
					if not (type_change_ok ctx.com e'.etype e.etype) then raise Not_found;
					e'
			in
			let rec commit e = match e.eexpr with
				| TLocal v when not v.v_capture ->
					begin try
						inline e v.v_id
					with Not_found ->
						e
					end
				| TBinop((OpAssign | OpAssignOp _ as op),({eexpr = TLocal v} as e1),e2) ->
					let e2 = try
						if (Optimizer.has_side_effect e1) then raise Not_found;
						inline e2 v.v_id
					with Not_found ->
						commit e2
					in
					{e with eexpr = TBinop(op,e1,e2)}
				| TVar(v,Some e1) when not (Optimizer.has_side_effect e1) ->
					let e1 = try inline e1 v.v_id with Not_found -> commit e1 in
					{e with eexpr = TVar(v,Some e1)}
				| _ ->
					Type.map_expr commit e
			in
			Graph.iter_dom_tree ctx.graph (fun bb ->
				dynarray_map commit bb.bb_el
			);
	end)

	(*
		Propagates local variables to other local variables.

		Respects scopes on targets where it matters (all except JS and As3).
	*)
	module CopyPropagation = DataFlow(struct
		open BasicBlock
		open Graph

		type t =
			| Top
			| Bottom
			| Local of tvar

		let to_string = function
			| Top -> "Top"
			| Bottom -> "Bottom"
			| Local v -> Printf.sprintf "%s<%i>" v.v_name v.v_id

		let conditional = false
		let flag = FlagCopyPropagation
		let lattice = Hashtbl.create 0

		let get_cell i = try Hashtbl.find lattice i with Not_found -> Top
		let set_cell i ct = Hashtbl.replace lattice i ct

		let top = Top
		let bottom = Bottom

		let equals t1 t2 = match t1,t2 with
			| Top,Top -> true
			| Bottom,Bottom -> true
			| Local v1,Local v2 -> v1.v_id = v2.v_id
			| _ -> false

		let transfer ctx bb e =
			let rec loop e = match e.eexpr with
				| TLocal v when not v.v_capture ->
					Local v
				| TParenthesis e1 | TMeta(_,e1) | TCast(e1,None) ->
					loop e1
				| _ ->
					Bottom
			in
			loop e

		let init ctx =
			Hashtbl.clear lattice

		let commit ctx =
			let rec commit bb e = match e.eexpr with
				| TLocal v when not v.v_capture ->
					begin try
						let lat = get_cell v.v_id in
						let leave () =
							Hashtbl.remove lattice v.v_id;
							raise Not_found
						in
						let v' = match lat with Local v -> v | _ -> leave() in
						if not (type_change_ok ctx.com v'.v_type v.v_type) then leave();
						let v'' = get_var_origin ctx.graph v' in
						(* This restriction is in place due to how we currently reconstruct the AST. Multiple SSA-vars may be turned back to
						   the same origin var, which creates interference that is not tracked in the analysis. We address this by only
						   considering variables whose origin-variables are assigned to at most once. *)
						let writes = (get_var_info ctx.graph v'').vi_writes in
						begin match writes with
							| [bb'] when in_scope bb bb' -> ()
							| _ -> leave()
						end;
						commit bb {e with eexpr = TLocal v'}
					with Not_found ->
						e
					end
				| TBinop((OpAssign | OpAssignOp _ as op),({eexpr = TLocal _} as e1),e2) ->
					let e2 = commit bb e2 in
					{e with eexpr = TBinop(op,e1,e2)}
				| _ ->
					Type.map_expr (commit bb) e
			in
			Graph.iter_dom_tree ctx.graph (fun bb ->
				dynarray_map (commit bb) bb.bb_el
			);
	end)

	module CodeMotion = DataFlow(struct
		open Graph
		open BasicBlock

		let conditional = false
		let flag = FlagCodeMotion
			type t_def =
			| Top
			| Bottom
			| Const of tconstant
			| Local of tvar
			| Binop of binop * t * t

		and t = (t_def * Type.t * pos)

		let top = (Top,t_dynamic,null_pos)
		let bottom = (Bottom,t_dynamic,null_pos)

		let rec equals (lat1,_,_) (lat2,_,_) = match lat1,lat2 with
			| Top,Top
			| Bottom,Bottom ->
				true
			| Const ct1,Const ct2 ->
				ct1 = ct2
			| Local v1,Local v2 ->
				v1 == v2
			| Binop(op1,lat11,lat12),Binop(op2,lat21,lat22) ->
				op1 = op2 && equals lat11 lat21 && equals lat12 lat22
			| _ ->
				false

		let lattice = Hashtbl.create 0

		let get_cell i = try Hashtbl.find lattice i with Not_found -> top
		let set_cell i ct = Hashtbl.replace lattice i ct

		let rec transfer ctx bb e =
			let rec eval e = match e.eexpr with
				| TConst ct ->
					Const ct
				| TLocal v ->
					Local v
				| TBinop(op,e1,e2) ->
					let lat1 = transfer ctx bb e1 in
					let lat2 = transfer ctx bb e2 in
					Binop(op,lat1,lat2)
				| _ ->
					raise Exit
			in
			try
				(eval e,e.etype,e.epos)
			with Exit | Not_found ->
				bottom

		let init ctx =
			Hashtbl.clear lattice

		let commit ctx =
			let rec filter_loops lat loops = match lat with
				| Local v,_,_ ->
					let bb = match (get_var_info ctx.graph v).vi_writes with [bb] -> bb | _ -> raise Exit in
					let loops2 = List.filter (fun i -> not (List.mem i bb.bb_loop_groups)) loops in
					if loops2 = [] then filter_loops (get_cell v.v_id) loops else true,lat,loops2
				| Const _,_,_ ->
					false,lat,loops
				| Binop(op,lat1,lat2),t,p ->
					let has_local1,lat1,loops = filter_loops lat1 loops in
					let has_local2,lat2,loops = filter_loops lat2 loops in
					has_local1 || has_local2,(Binop(op,lat1,lat2),t,p),loops
				| _ ->
					raise Exit
			in
			let rec to_texpr (lat,t,p) =
				let def = match lat with
					| Local v -> TLocal v
					| Const ct -> TConst ct
					| Binop(op,lat1,lat2) -> TBinop(op,to_texpr lat1,to_texpr lat2)
					| _ -> raise Exit
				in
				{ eexpr = def; etype = t; epos = p }
			in
			let cache = Hashtbl.create 0 in
			let replace decl bb v =
				let lat,t,p = get_cell v.v_id in
				match lat with
				| Binop(op,lat1,lat2) ->
					let has_local1,lat1,loops = filter_loops lat1 bb.bb_loop_groups in
					let has_local2,lat2,loops = filter_loops lat2 loops in
					if loops = [] || not (has_local1 || has_local2) then raise Exit;
					let lat = ((Binop(op,lat1,lat2)),t,p) in
					let bb_loop_pre = IntMap.find (List.hd loops) ctx.graph.g_loops in
					let v' = try
						let l = Hashtbl.find cache bb_loop_pre.bb_id in
						snd (List.find (fun (lat',e) -> equals lat lat') l)
					with Not_found ->
						let v' = if decl then begin
							v
						end else begin
							let v' = alloc_var ctx.temp_var_name v.v_type in
							declare_var ctx.graph v' bb_loop_pre;
							v'.v_meta <- [Meta.CompilerGenerated,[],p];
							v'
						end in
						let e = to_texpr lat in
						let e = mk (TVar(v',Some e)) ctx.com.basic.tvoid p in
						add_texpr ctx.graph bb_loop_pre e;
						set_var_value ctx.graph v' bb_loop_pre false (DynArray.length bb_loop_pre.bb_el - 1);
						Hashtbl.replace cache bb_loop_pre.bb_id ((lat,v') :: try Hashtbl.find cache bb_loop_pre.bb_id with Not_found -> []);
						v'
					in
					let ev' = mk (TLocal v') v'.v_type p in
					if decl then begin
						if v == v' then
							mk (TConst TNull) t p
						else
							mk (TVar(v,Some ev')) ctx.com.basic.tvoid p
					end else begin
						let ev = mk (TLocal v) v.v_type p in
						mk (TBinop(OpAssign,ev,ev')) t p
					end
				| _ ->
					raise Exit
			in
			let rec commit bb e = match e.eexpr with
				| TBinop(OpAssign,({eexpr = TLocal v} as e1),e2) ->
					begin try
						replace false bb v
					with Exit ->
						{e with eexpr = TBinop(OpAssign,e1,commit bb e2)}
					end
				| TVar(v,Some e1) when Meta.has Meta.CompilerGenerated v.v_meta ->
					begin try
						replace true bb v
					with Exit ->
						{e with eexpr = TVar(v,Some (commit bb e1))}
					end
				| _ ->
					Type.map_expr (commit bb) e
			in
			Graph.iter_dom_tree ctx.graph (fun bb ->
				if bb.bb_loop_groups <> [] then dynarray_map (commit bb) bb.bb_el
			);
	end)

	module LoopInductionVariables = struct
		open Graph

		type book = {
			tvar : tvar;
			index : int;
			mutable lowlink : int;
			mutable on_stack : bool
		}

		let find_cycles g =
			let index = ref 0 in
			let s = ref [] in
			let book = ref IntMap.empty in
			let add_book_entry v =
				let entry = {
					tvar = v;
					index = !index;
					lowlink = !index;
					on_stack = true;
				} in
				incr index;
				book := IntMap.add v.v_id entry !book;
				entry
			in
			let rec strong_connect vi =
				let v_entry = add_book_entry vi.vi_var in
				s := v_entry :: !s;
				List.iter (fun (bb,is_phi,i) ->
					try
						let e = get_texpr g bb is_phi i in
						let w = match e.eexpr with
							| TVar(v,_) | TBinop(OpAssign,{eexpr = TLocal v},_) -> v
							| _ -> raise Exit
						in
						begin try
							let w_entry = IntMap.find w.v_id !book in
							if w_entry.on_stack then
								v_entry.lowlink <- min v_entry.lowlink w_entry.index
						with Not_found ->
							let w_entry = strong_connect (get_var_info g w) in
							v_entry.lowlink <- min v_entry.lowlink w_entry.lowlink;
						end
					with Exit ->
						()
				) vi.vi_ssa_edges;
				if v_entry.lowlink = v_entry.index then begin
					let rec loop acc entries = match entries with
						| w_entry :: entries ->
							w_entry.on_stack <- false;
							if w_entry == v_entry then w_entry :: acc,entries
							else loop (w_entry :: acc) entries
						| [] ->
							acc,[]
					in
					let scc,rest = loop [] !s in
					begin match scc with
						| [] | [_] ->
							()
						| _ ->
							print_endline "SCC:";
							List.iter (fun entry -> print_endline (Printf.sprintf "%s<%i>" entry.tvar.v_name entry.tvar.v_id)) scc;
							(* now what? *)
					end;
					s := rest
				end;
				v_entry
			in
			DynArray.iter (fun vi -> match vi.vi_ssa_edges with
				| [] ->
					()
				| _ ->
					if not (IntMap.mem vi.vi_var.v_id !book) then
						ignore(strong_connect vi)
			) g.g_var_infos

		let apply ctx =
			find_cycles ctx.graph
	end

	(*
		LocalDce implements a mark & sweep dead code elimination. The mark phase follows the CFG edges of the graphs to find
		variable usages and marks variables accordingly. If ConstPropagation was run before, only CFG edges which are
		considered executable are processed.

		If a variable is marked as used, its reaching definition is recursively marked as used too. Furthermore its
		value is processed as an expression.

		The sweep phase removes all variable declarations and assignments of unused variables, keeping only the assigned
		expression in case of side-effects.
	*)
	module LocalDce = struct
		open BasicBlock
		open Graph
		open Config

		let rec has_side_effect e =
			let rec loop e =
				match e.eexpr with
				| TConst _ | TLocal _ | TTypeExpr _ | TFunction _ -> ()
				| TCall ({ eexpr = TField(_,FStatic({ cl_path = ([],"Std") },{ cf_name = "string" })) },args) -> Type.iter loop e
				| TCall ({eexpr = TField(_,FEnum _)},_) -> Type.iter loop e
				| TCall ({eexpr = TConst (TString ("phi" | "fun"))},_) -> ()
				| TNew _ | TCall _ | TBinop ((OpAssignOp _ | OpAssign),_,_) | TUnop ((Increment|Decrement),_,_) -> raise Exit
				| TReturn _ | TBreak | TContinue | TThrow _ | TCast (_,Some _) -> raise Exit
				| TFor _ -> raise Exit
				| TArray _ | TEnumParameter _ | TCast (_,None) | TBinop _ | TUnop _ | TParenthesis _ | TMeta _ | TWhile _
				| TField _ | TIf _ | TTry _ | TSwitch _ | TArrayDecl _ | TBlock _ | TObjectDecl _ | TVar _ -> Type.iter loop e
			in
			try
				loop e;
				false
			with Exit ->
				true

		let rec apply ctx =
			let is_used v =
				Meta.has Meta.Used v.v_meta
			in
			let keep v =
				is_used v || (not (Meta.has Meta.CompilerGenerated v.v_meta) && not ctx.config.local_dce) || is_ref_type v.v_type || v.v_capture || Meta.has Meta.This v.v_meta
			in
			let rec use v =
				if not (is_used v) then begin
					v.v_meta <- (Meta.Used,[],null_pos) :: v.v_meta;
					(try expr (get_var_value ctx.graph v) with Not_found -> ());
					begin match Ssa.get_reaching_def ctx.graph v with
						| None -> use (get_var_origin ctx.graph v)
						| Some v -> use v;
					end
				end
			and expr e = match e.eexpr with
				| TLocal v when not (is_unbound v) ->
					use v;
				| TBinop(OpAssign,{eexpr = TLocal v},e1) | TVar(v,Some e1) when not (is_unbound v) ->
					if has_side_effect e1 || keep v then expr e1
					else ()
				| _ ->
					Type.iter expr e
			in

			let rec mark bb =
				DynArray.iter expr bb.bb_el;
				DynArray.iter expr bb.bb_phi;
				List.iter (fun edge ->
					if not (has_flag edge FlagDce) then begin
						edge.cfg_flags <- FlagDce :: edge.cfg_flags;
						if not ctx.config.const_propagation || has_flag edge FlagExecutable then
							mark edge.cfg_from;
					end
				) bb.bb_incoming
			in
			mark ctx.graph.g_exit;
			let rec sweep e = match e.eexpr with
				| TBinop(OpAssign,{eexpr = TLocal v},e2) | TVar(v,Some e2) when not (keep v) ->
					if has_side_effect e2 then
						e2
					else
						mk (TConst TNull) e.etype e.epos
				| TVar(v,None) when not (keep v) ->
					mk (TConst TNull) e.etype e.epos
				| _ ->
					Type.map_expr sweep e
			in
			Graph.iter_dom_tree ctx.graph (fun bb ->
				dynarray_map sweep bb.bb_el
			);
	end


	module TCE = struct
		open BasicBlock
		open Graph

		type tce_mode =
			| TCEStrict


		type 'a result =
			| RValue of 'a
			| RError of string

		type fdata_kind =
			| FKStatic of tclass * tclass_field
			| FKInstance of tclass * tclass_field
			| FKLocal

		type fdata = {
			f_index        : int;                                   (* the index used for the switch *)
			f_tf           : tfunc;
			f_call_var_m   : (int,tvar) PMap.t;                     (* the local var used as tmp var to 'call' this function *)
			f_call_vars    : (tvar * tvar * tconstant option) list; (* list of argument * call_tmp_var * optional value *)
			f_bb_begin     : BasicBlock.t;                          (* relevant blocks *)
			f_bb_end       : BasicBlock.t;
			f_bb_decl      : BasicBlock.t option;
			mutable f_is_entry : bool;
			mutable f_kind : fdata_kind;                            (* defaults to FKLocal, needs to be changed after *)
		(*	f_exclude   : bool;               (* exclude from transformation *)
			f_selfrec   : bool;               (* does it call itself? *)
			f_mutualrec : bool;               (* does it call others in the same group? *) *)
		}

		let mk_fdata f_index f_tf f_call_var_m f_call_vars f_bb_begin f_bb_end f_bb_decl f_kind =
			{ f_index; f_tf; f_call_var_m; f_call_vars; f_bb_begin; f_bb_end; f_bb_decl; f_is_entry=false; f_kind }

		type mctx = {
			mutable funcs_by_vid : (int, fdata) PMap.t;
			mutable funcs_by_idx : (int, fdata) PMap.t;
			mutable funcs_by_bbid: (int, fdata) PMap.t;
			mutable funcs_by_field : (int, fdata) PMap.t;
			mutable captured_vars : (int,tvar) PMap.t;
			mutable recursive_calls : (int,(BasicBlock.t * int * fdata * texpr list * texpr option)) PMap.t;
			(* bb * idx * fdata * args * `this`*)
			actx : analyzer_context
		}

		let debug = false

		let original_var_id ctx v =
			let vo = Graph.get_var_origin ctx.actx.graph v in
			vo.v_id

		let foldi f acc l =
			let rec loop i acc xs = (match xs with
					| [] -> acc
					| x :: xs -> let acc = f i acc x in loop (i+1) acc xs
				)
			in loop 0 acc l

		let dopsid s id = print_endline (Printf.sprintf "%s id: %d " s id)
		let p_s_id s id = if debug then dopsid s id

		(* TODO migrate into Graph ? *)

		let iter_dom_sub_tree bb_start bb_term f =
			let rec loop bb =
				if bb.bb_id != bb_term.bb_id then begin
					f bb;
					List.iter  loop bb.bb_dominated
				end else ()
			in loop bb_start

		let fold_dom_tree bb bb_term f acc =
			let rec loop acc bb =
				let acc = f acc bb in
				if bb.bb_id != bb_term.bb_id then
					List.fold_left loop acc bb.bb_dominated
				else
					acc
			in loop acc bb

		let fold_dom_tree_filter filter f acc bb =
			let rec loop acc bb =
				let acc = f acc bb in
				List.fold_left loop acc (List.filter filter bb.bb_dominated)
			in loop acc bb

		let get_func_end_block bb_begin =  begin match (
				fold_dom_tree_filter
				(fun bb -> match bb.bb_kind with BKFunctionBegin -> false | _ -> true )
				(fun acc bb -> match bb.bb_kind with BKFunctionEnd -> bb :: acc | _ -> acc)
				[]
				bb_begin
			) with
				| [bb] -> bb
				| _ -> assert false (* invalid assumption *)
			end

		let get_func_decl_block bb_begin = (match bb_begin.bb_incoming with
			| [{cfg_from=bb;cfg_kind=CFGFunction}] -> bb
			| _ -> assert false (*invalid assumption*)
		)


		(* TODO make independent from a single graph *)
		let mk_func_maps mctx = begin
			let g = mctx.actx.graph in
			let f_ord = List.sort compare (Hashtbl.fold (fun bb_id _ acc -> bb_id :: acc ) g.g_functions []) in
			let (bbm,idxm) = foldi ( fun idx (bbm,idxm) bb_id ->
				let (bb,t,pos,tf) = Hashtbl.find g.g_functions bb_id in

				let bb_end  = get_func_end_block bb in

				let bb_decl =
					let bb_decl = get_func_decl_block bb in
					if bb_decl.bb_id = g.g_root.bb_id then None else Some(bb_decl) in

				let (call_vars_rev,call_var_m) = List.fold_left ( fun (l,m) (v,co) ->
						let cv = alloc_var (Printf.sprintf "_tce_%d_%s" idx v.v_name) v.v_type in (* allocating the call tmp vars here *)
						let m = PMap.add v.v_id cv m in
						let l = (v,cv,co) :: l in
						(l,m)
					) ([],PMap.empty) tf.tf_args in
				let call_vars = List.rev call_vars_rev in
				let fdata = mk_fdata idx tf call_var_m call_vars bb bb_end bb_decl FKLocal in
				(PMap.add bb_id fdata bbm),(PMap.add idx fdata idxm)

			) (PMap.empty,PMap.empty) f_ord in
			mctx.funcs_by_idx <- idxm;
			mctx.funcs_by_bbid <- bbm
		end

		let add_func_by_vid mctx vid bb_id =
			mctx.funcs_by_vid <- PMap.add vid (PMap.find bb_id mctx.funcs_by_bbid) mctx.funcs_by_vid

		let find_func_by_vid mctx vid =
			( try Some(PMap.find vid mctx.funcs_by_vid) with Not_found -> None )

		let add_func_by_field mctx c cf bb_id is_entry = begin
			let fid = Hashtbl.hash (c.cl_path,cf.cf_name) in
			let kind = if PMap.exists cf.cf_name c.cl_statics then FKStatic(c,cf) else FKInstance(c,cf) in
			let fdata = (PMap.find bb_id mctx.funcs_by_bbid) in
			fdata.f_kind <- kind;
			fdata.f_is_entry <- is_entry;
			mctx.funcs_by_field <- PMap.add fid fdata mctx.funcs_by_field
		end

		let find_func_by_field mctx c cf =
			let fid = Hashtbl.hash (c.cl_path,cf.cf_name) in
			( try Some(PMap.find fid mctx.funcs_by_field) with Not_found -> None )

		let p_tree_ids bb = if debug then print_endline (Printf.sprintf "bb.id::%d" bb.bb_id)

			(* 1. modify function-begin
			*    declare + assign call-replacement variables, 1 for each argument, and optionally `this`
			* 2. insert while (true/cond) block after start
			* 3. insert loop-head block after while-start block
			* 4. insert switch after loop-head
			* 5. insert one case for each mutual recursive function
			*      5.1 transfer the statements from function-begin into the respective case block
			*          transfer outgoing edges from function-begin to case block
			* 6. replace all occurences of recursive calls with assignments to the respective locals that replace
			*    the arguments
			* 7. replace all goto function-ends with gotos to loop-head for the recursive calls
			* *)

		let replace_dominator mctx bb_old bb_dom bb_term =
			let g = mctx.actx.graph in
			let replace bb = bb.bb_dominator.bb_id = bb_old.bb_id in
			let dominated = fold_dom_tree bb_old bb_term ( fun acc bb ->
				if replace bb then begin
					bb.bb_dominator <- bb_dom;
					bb :: acc
					end
				else acc
			) [] in
			print_endline (Printf.sprintf "replacing old_dom %d with %d " bb_old.bb_id bb_dom.bb_id);
			List.iter (fun bb -> print_endline (Printf.sprintf "  replaced dom of %d with %s "  bb.bb_id (s_block_kind bb.bb_kind)) )dominated;
			(* now, remove all dominated blocks from bb_old, before we remove bb_old itself  *)
			bb_old.bb_dominated <- [];
			(* bb_old.bb_dominator.bb_dominated  <- List.filter (fun bb -> if bb.bb_id = bb_ld.bb_id then false else true ) bb_old.bb_dominator.bb_dominated;  *)
			dominated

		let transform mctx bb_dom  =
			let g = mctx.actx.graph in
			let tvoid = mctx.actx.com.basic.tvoid  in
			let tint = mctx.actx.com.basic.tint in
			let tbool = mctx.actx.com.basic.tbool in
			let define_var bb v value =
				declare_var g v bb;
				add_var_def g bb v;
				let e = mk (TVar( v, value)) tvoid null_pos in
				Graph.add_texpr g bb e
			in

			let mk_local v = mk(TLocal v) v.v_type null_pos in

			let close_blocks l = List.iter (fun bb -> bb.bb_closed <- true ) l in

			let fdata_entry = PMap.find bb_dom.bb_id mctx.funcs_by_bbid in

			(* let bb_next bb = create_node g BKNormal bb bb.bb_type bb.bb_pos in *)

			(*   structure   *)
			let bb_fake = BasicBlock._create (alloc_id()) BKUnreachable [] tvoid null_pos in
			let bb_setup = (* scope 0 declarations, etc *)
				(*we first leave the node "unconnected" and set the dom later *)
				create_node g BKNormal [0] bb_fake tvoid null_pos in

			let bb_while = Graph.create_node g BKNormal [0] bb_setup tvoid null_pos in
			let bb_loophead = Graph.create_node g BKLoopHead [0] bb_while tvoid null_pos in
			let bb_switch = Graph.create_node g BKNormal [0] bb_loophead bb_dom.bb_type null_pos in

			Graph.add_cfg_edge g bb_setup bb_while CFGGoto;
			Graph.add_cfg_edge g bb_while bb_loophead CFGGoto;
			Graph.add_cfg_edge g bb_loophead bb_switch CFGGoto;


			Graph.set_syntax_edge g bb_while (SEWhile(bb_switch,g.g_unreachable));

			(* declare/define tmp call vars, captured vars and arguments outside the main loop in bb_setup  *)

			PMap.iter ( fun idx f ->
				List.iter ( fun (v,cv,co) ->
					let value = if f.f_is_entry then
						Some(mk_local v)
					else begin
						v.v_name <- (Printf.sprintf "_arg%d_%s" idx v.v_name); (* unique name for non-entry function args *)
						define_var bb_setup v None;
						None
					end in
					define_var bb_setup cv value;
				) f.f_call_vars;
			) mctx.funcs_by_idx;

			PMap.iter ( fun id v ->
				(* exclude entry function arguments and the local functions themselves *)
				if not ((PMap.exists v.v_id fdata_entry.f_call_var_m) || (PMap.exists (original_var_id mctx v) mctx.funcs_by_vid)) then
					let oid = original_var_id mctx v in
					v.v_name <-  (Printf.sprintf "_tce_cap_%d_%s" oid v.v_name); (* give it a horrible unique name *)
					define_var bb_setup v None;
			) mctx.captured_vars;

			(* hook up entry function begin block - only write after bb_cases are set up *)

			set_syntax_edge g bb_setup (SEMerge bb_while);
			let cfgs = List.filter ( fun ce -> (match ce.cfg_kind with CFGFunction -> true | _ -> false )) bb_dom.bb_outgoing in
			let rewrite_dom_edges = (fun () ->
					set_syntax_edge g bb_dom (SEMerge bb_setup);
					bb_dom.bb_outgoing <- [];                    (* EDGE *)
					Graph.add_cfg_edge g bb_dom bb_setup CFGGoto;


					bb_setup.bb_dominator <- bb_dom;
					bb_while.bb_dominator <- bb_setup;
					bb_loophead.bb_dominator <- bb_while;
					bb_switch.bb_dominator <- bb_loophead;

					bb_dom.bb_dominated <- [bb_setup];
					bb_setup.bb_dominated <- [bb_while];
					bb_while.bb_dominated <- [bb_loophead];
					bb_loophead.bb_dominated <- [bb_switch];
				(* switch dominates all the bb_case nodes *)
			) in

			(* add while(true) *)
			let etrue = mk (TConst(TBool true)) tbool null_pos in
			let ewhile = mk (TWhile(etrue,etrue(*whatever*),NormalWhile)) tvoid null_pos in
			add_texpr g bb_while ewhile;

			(* switch branch *)
			let mk_int i =  (mk (TConst( TInt(Int32.of_int i)))  tint null_pos) in
			let tce_loop_var =
					alloc_var "_hx_tce_current_function" tint in

			define_var bb_setup tce_loop_var (Some (mk (TConst( TInt(Int32.of_int fdata_entry.f_index)))  tint null_pos));

			add_texpr g bb_switch (wrap_meta ":cond-branch" (mk (TLocal(tce_loop_var)) tce_loop_var.v_type null_pos));

			p_s_id "bb_setup " bb_setup.bb_id;
			p_s_id "bb_while " bb_while.bb_id;
			p_s_id "bb_loophead " bb_loophead.bb_id;
			p_s_id "bb_switch " bb_switch.bb_id;

			let assign_var v evalue =
				let ev = mk (TLocal v) v.v_type null_pos in
				mk (TBinop(OpAssign,ev,evalue)) v.v_type null_pos
			in

			let bb_cases = PMap.foldi ( fun idx fdata acc  -> ( (* each case corresponds to one of the functions tce is being applied to *)

				let bb_case = Graph.create_node g BKConditional [idx;0] bb_switch bb_dom.bb_type null_pos in
				let te = mk (TConst (TInt (Int32.of_int idx))) t_dynamic null_pos in

				Graph.add_cfg_edge g bb_switch bb_case (CFGCondBranch te);

				let load_call_args fdata = List.iter (fun (v,cv,co) ->
					add_texpr g bb_case (assign_var v (mk_local cv));
				) fdata.f_call_vars;
				in
				let transfer_statements bbf bbt tf = (* TODO : transform `this` *)
					(* when we're transferring TVars, do we have to declare_var them in the new block?*)
					DynArray.iter ( fun e -> Graph.add_texpr g bb_case e ) bbf.bb_el;
				in

				let filter_func_cfges ce = (match ce with
					| {cfg_kind=CFGFunction;cfg_to=cfg_to} -> if (PMap.exists cfg_to.bb_id mctx.funcs_by_bbid) then false else true
					| _ -> true
				) in

				let transfer_edges bbf bbt tf =
					let cfges = List.filter filter_func_cfges bbf.bb_outgoing in
					List.iter ( fun ce ->
						 Graph.add_cfg_edge g bb_case ce.cfg_to ce.cfg_kind
					) cfges;
					Graph.set_syntax_edge g bb_case bbf.bb_syntax_edge
				in
				let rewrite_func_end_blocks bbf bbfend tf =
					(* all incoming edges of bfend need to be redirected to the end of the main function or
					* to the loop header *)
					let blocks = List.map (fun ce -> ce.cfg_from) bbfend.bb_incoming in
					dopsid (String.concat "," (List.map (fun b -> string_of_int b.bb_id) blocks )) 8;
					List.iter ( fun bb ->

						(* if bb.bb_id is in recursive_calls we have to rewrite the call,
						 * if not we contiue below in Not_found *)

						try let calldata = PMap.find bb.bb_id mctx.recursive_calls in
							let (bb,call_idx,fdata_callee,args,othis) = calldata in
							(* got a recursive call here - rewrite it *)
							(* 1. remove call *)
							DynArray.delete bb.bb_el call_idx;
							List.iter (fun ((v,cv,co),evalue) ->
								let e = assign_var cv evalue in
								add_texpr g bb e;
								add_var_def g bb cv;
							) (List.combine fdata_callee.f_call_vars args);

							let e = assign_var tce_loop_var (mk_int fdata_callee.f_index) in
							add_texpr g bb e;
							add_var_def g bb tce_loop_var;

							(match bb.bb_outgoing with
								| [{cfg_kind=kind}] ->
									bb.bb_outgoing <-
										[{cfg_from=bb;cfg_to=bb_loophead;cfg_kind=kind;cfg_flags=[]}];
								| _ -> assert false ) (* assumption there can be just one is wrong :/ *)

						with Not_found -> begin (* no recursive call here, only adjust the edges *)
							let outgoing = List.map ( fun ce ->
								dopsid "rewriting outgoing" bb.bb_id;
								if ce.cfg_to.bb_id = bbfend.bb_id && ce.cfg_to.bb_id != g.g_exit.bb_id then
										{ ce with cfg_to = g.g_exit }
								else
										ce
							) bb.bb_outgoing in
							dopsid "rewritten outgoing" bb.bb_id;
							bb.bb_outgoing <- outgoing;
							dopsid "assigned it" bb.bb_id;
							end
							(* syntax edge should be OK here *)
						) blocks;
					in
				let declare_args bbf bbt tf = List.iter ( fun (v,oc) ->
						let value = Option.map ( fun c -> mk (TConst c) v.v_type null_pos ) oc in

						define_var bb_setup v value;
					) tf.tf_args; (* declare them outside the loop *)
				in

				let (bbf,bbfend,tf,decl) =  (fdata.f_bb_begin,fdata.f_bb_end,fdata.f_tf,false) in

				let rewrite_dominators = (fun () ->
					bb_case.bb_dominator <- bb_switch;
					dopsid "replace" bb_case.bb_id;
					bb_case.bb_dominated <- replace_dominator mctx fdata.f_bb_begin bb_case fdata.f_bb_end;
					dopsid "replace" bb_case.bb_id;
				) in
				load_call_args fdata;
				transfer_statements bbf bbfend tf;
				transfer_edges bbf bbfend tf;
				if decl then declare_args bbf bbfend tf;
				rewrite_func_end_blocks bbf bbfend tf;
				bb_case.bb_closed <- true;
				(bb_case,te,rewrite_dominators) :: acc
			)) mctx.funcs_by_idx [] in


			let p_dom_tree nmap =
				let nodes_map = fold_dom_tree g.g_root g.g_exit (fun m bb ->
					let _ = try let n = PMap.find bb.bb_id nmap in
							dopsid ("checking " ^ n) bb.bb_id
						with Not_found ->
							dopsid (
								Printf.sprintf "checking unknown with dom %d  and kind %s \n  [%s] "
								bb.bb_dominator.bb_id
								(BasicBlock.s_block_kind bb.bb_kind)
								(String.concat "," (List.map (fun bb -> (string_of_int bb.bb_id)) bb.bb_dominated ))
							) bb.bb_id
					in
					if PMap.exists bb.bb_id m then begin
						try let n = PMap.find bb.bb_id nmap in
							dopsid n bb.bb_id;
							assert false;
						with Not_found ->
							dopsid "seen block already" bb.bb_id;
							assert false;
						end else
							PMap.add bb.bb_id 0 m
				) PMap.empty in ()
			in
			let bb_cases_data = bb_cases in
			let bb_cases = List.map (fun (b,_,_) -> b) bb_cases_data in


			let all_blocks = [bb_setup;bb_while;bb_loophead;bb_switch] in
			let bb_names = ["setup";"while";"loophead";"switch"] in
			let nmap = List.fold_left (fun m (bb,n) -> PMap.add bb.bb_id n m) PMap.empty (List.combine all_blocks bb_names) in
			let nmap = List.fold_left (fun m bb -> PMap.add bb.bb_id "bb_case" m) nmap bb_cases in

			let switchcases = List.map (fun (bb_case,te,_) -> [te],bb_case ) (List.rev bb_cases_data) in
			Graph.set_syntax_edge g bb_switch (SESwitch(switchcases,None,g.g_unreachable));

			p_dom_tree nmap;

			(*the order of the following two is important *)
			List.iter ( fun (_,_,rewrite_dominators) -> rewrite_dominators ()) bb_cases_data;
			rewrite_dom_edges ();
			bb_switch.bb_dominated <- bb_cases;

			p_dom_tree nmap;

			close_blocks [bb_setup;bb_while;bb_loophead;bb_switch];
			close_blocks bb_cases;

			(* clean up - turn all captured var definitions into assignments
			 * remove all eliminated functions *)
			let enull = mk(TConst(TNull)) tvoid null_pos in
			dopsid "cleanup" 0;
			iter_dom_tree g (fun bb ->

				PMap.iter (fun idx f -> List.iter ( fun (v,cv,_) -> add_var_def g bb v; add_var_def g bb cv ) f.f_call_vars ) mctx.funcs_by_idx

			);
			iter_dom_tree g (fun bb ->
				dopsid "cleanup node" bb.bb_id;
				dynarray_map (fun e -> (match e.eexpr with
					| TVar(v,_)
					| TBinop(OpAssign,{eexpr=TLocal v},_) ->
							let oid = (original_var_id mctx v) in
							if Option.is_some (find_func_by_vid mctx oid) then enull else e
					| _ -> e
				) ) bb.bb_el;
			);
			dopsid "cleanup" 1;

			iter_dom_tree g (fun bb ->
				(* obviously exclude bb_setup here *)
				if bb.bb_id = bb_setup.bb_id then () else
				dynarray_map (fun e -> (match e.eexpr with
					| TVar(v,eo) ->
						let oid = (original_var_id mctx v) in
						if (PMap.exists oid mctx.captured_vars) then begin
							add_var_def g bb v;
							Option.map_default ( fun evalue -> assign_var v evalue) enull eo
						end	else
							e
					| TBinop(OpAssign,{eexpr=TLocal v},_) ->
							let oid = (original_var_id mctx v) in
							if Option.is_some (find_func_by_vid mctx oid) then enull else e
					| _ -> e
				) ) bb.bb_el;
			);
			dopsid "cleanup" 2;
			()


		let field_id c cf = Hashtbl.hash (c.cl_path,cf.cf_name)
		let is_tce_call mctx e =
			(match e.eexpr with
			| TCall({eexpr=TLocal v},args) ->
					Option.map (fun fdata -> fdata,args,None ) (find_func_by_vid mctx (original_var_id mctx v))
			| TCall({eexpr= TField(ethis, FInstance(c,_,cf))},args) ->
					Option.map (fun fdata -> fdata,args, (Some ethis) ) (find_func_by_field mctx c cf)
			| TCall({eexpr= TField(_ , ( FStatic(c,cf)) )},args ) ->
					(*mctx.actx.com.warning (" recursive call " ^ (s_expr_pretty e)) e.epos;*)
					Option.map (fun fdata -> fdata,args,None ) (find_func_by_field mctx c cf)
			| _ -> None )

		let has_tce_call mctx e =
			let rec loop e = (match e.eexpr with
				| TCall(_,_) -> is_tce_call mctx e
				| TVar(_, Some te)
				| TBinop(OpAssign,_,te)
				| TReturn(Some te) -> loop te
				| _ -> None)
			in loop e

		let add_local_func mctx bb idx e = (match e.eexpr with
			| TVar ( v,
				Some({eexpr=TCall({eexpr = TConst (TString "fun")},[{eexpr = TConst (TInt i32)}])}))
			| TBinop (OpAssign,(
				{eexpr=TLocal v}),
				{eexpr=TCall({eexpr = TConst (TString "fun")},[{eexpr = TConst (TInt i32)}])}) ->
				let oid = (original_var_id mctx v) in
				if true then print_endline (Printf.sprintf "### adding local function %d %s " oid  (v.v_name));

				let bb_func_id = (Int32.to_int i32) in
				add_func_by_vid mctx (original_var_id mctx v) bb_func_id;
				(match (DynArray.get bb.bb_el (idx+1)).eexpr with
					| TVar(vleft,Some({eexpr=TLocal v2})) when (v2.v_id = v.v_id) ->
						let oid = (original_var_id mctx vleft) in
						print_endline (Printf.sprintf "### + %d %s " oid  (v.v_name));
						add_func_by_vid mctx (original_var_id mctx vleft) bb_func_id;
					| _ -> ());

			| _ -> ())
		let warn_invalid_calls ctx l  =
			List.iter (fun (bb,idx,_,_,_) ->
				let e = DynArray.get bb.bb_el idx in
				(ctx.com.warning "call not in tail position" e.epos )
			) (List.rev l)


		let edge_to_exit bb = (match bb.bb_outgoing with
			| [{cfg_to={bb_kind = BKFunctionEnd }}] -> true
			| _ -> false)

		let fold_recursive_calls mctx bb_entry_func f acc =
			let g = mctx.actx.graph in
			fold_dom_tree bb_entry_func g.g_exit (fun acc bb ->
				let len = DynArray.length bb.bb_el in
				let rec loop idx acc =
					if idx = len then
						acc
					else begin
						let te = DynArray.get bb.bb_el idx in
						add_local_func mctx bb idx te;
						let callo = (has_tce_call mctx te) in
						let acc = Option.map_default
							(fun (fdata,args,othis) -> (bb,idx,fdata,args,othis) :: acc ) acc callo
						in loop (idx+1) acc
					end
				in f bb (loop 0 []) acc
			) acc


		let rec apply ctx c cf = begin
			let mctx = {
				funcs_by_vid = PMap.empty;
				funcs_by_idx = PMap.empty;
				funcs_by_bbid= PMap.empty;
				funcs_by_field = PMap.empty;
				captured_vars =  PMap.empty;
				recursive_calls = PMap.empty;
				actx = ctx;
			} in

			let g = ctx.graph in

			let bb_entry_func = (match g.g_root.bb_outgoing with
				| [{cfg_to={bb_kind=BKFunctionBegin} as bb_entry_func}] -> bb_entry_func
				| _ -> assert false (* really?? *)
			) in

			mk_func_maps mctx;

			add_func_by_field mctx c cf bb_entry_func.bb_id true;

			let fdata_entry = Option.get (find_func_by_field mctx c cf) in

			mctx.captured_vars <- DynArray.fold_left ( fun acc vi ->
				(* exclude args of the entry function *)
				if vi.vi_origin.v_capture && not (PMap.exists vi.vi_origin.v_id fdata_entry.f_call_var_m) then
					PMap.add vi.vi_origin.v_id vi.vi_origin acc
				else
					acc
			) PMap.empty g.g_var_infos;

			(* for now (and later in strict mode) we handle any calls not in tail position as errors  *)
			let recursive_call_results =
				fold_recursive_calls mctx bb_entry_func ( fun bb rec_calls acc ->
					let len = DynArray.length bb.bb_el in
					let is_valid_tce_call (_,idx,_,_,_) = (idx = len-1) && edge_to_exit bb in
					let invalid = List.filter (fun c -> not (is_valid_tce_call c)) rec_calls in
					let res = (match invalid with
						| [] -> RValue rec_calls
						| l  -> warn_invalid_calls ctx l;
								RError "some calls were not in tail position - see above warnings for more."
					) in res :: acc
				) []
			in
			let recursive_calls = List.fold_left ( fun acc res -> (match res with
				| RError e -> error e cf.cf_pos;
				| RValue [calldata] ->  calldata :: acc
				| RValue [] -> acc
				| _ -> assert false )
			) [] recursive_call_results in

			mctx.recursive_calls <- List.fold_left ( fun m cd ->
				let (bb,_,_,_,_) = cd in PMap.add bb.bb_id cd m
			) PMap.empty recursive_calls;

			transform mctx bb_entry_func;

		end


	end

	module Debug = struct
		open BasicBlock
		open Graph

		type node_info =
			| NIExpr
			| NIVars
			| NIPhi
			| NILoopGroups
			| NIScopes

		let s_var v = Printf.sprintf "%s<%i>" v.v_name v.v_id

		let dot_debug_node g ch nil bb =
			let s = Printf.sprintf "(%i)" bb.bb_id in
			let s = List.fold_left (fun s ni -> s ^ match ni with
				| NIExpr -> if DynArray.length bb.bb_el = 0 then "" else "\n" ^  String.concat "\n" (DynArray.to_list (DynArray.map s_expr_pretty bb.bb_el))
				| NIPhi -> if DynArray.length bb.bb_phi = 0 then "" else "\n" ^ String.concat "\n" (DynArray.to_list (DynArray.map (fun e -> s_expr_pretty e) bb.bb_phi))
				| NIVars -> if bb.bb_var_writes = [] then "" else "\n" ^ String.concat ", " (List.map (fun v -> s_var v) bb.bb_var_writes)
				| NILoopGroups -> if bb.bb_loop_groups = [] then "" else "\nLoops: " ^ (String.concat ", " (List.map string_of_int bb.bb_loop_groups))
				| NIScopes -> if bb.bb_scopes = [] then "" else "\nScopes: " ^ (String.concat ", " (List.map string_of_int bb.bb_scopes))
			) s nil in
			let s_kind = match bb.bb_kind with
				| BKRoot -> "<root>\n"
				| BKFunctionBegin -> "<function-begin>\n"
				| BKFunctionEnd -> "<function-end>\n"
				| BKLoopHead -> "<loop-head>\n"
				| _ -> ""
			in
			Printf.fprintf ch "n%i [shape=box,label=\"%s%s\"];\n" bb.bb_id s_kind (s_escape s)

		let dot_debug_cfg_edge ch edge =
			let label = match edge.cfg_kind with
				| CFGGoto -> "goto"
				| CFGFunction -> "function"
				| CFGMaybeThrow -> "throw?"
				| CFGCondBranch _ -> "branch"
				| CFGCondElse -> "else"
			in
			let s_edge_flag = function
				| FlagExecutable -> "exe"
				| FlagDce -> "dce"
				| FlagCodeMotion -> "motion"
				| FlagCopyPropagation -> "copy"
			in
			let label = label ^ match edge.cfg_flags with
				| [] -> ""
				| _ -> Printf.sprintf " [%s]" (String.concat ", " (List.map s_edge_flag edge.cfg_flags))
			in
			Printf.fprintf ch "n%i -> n%i[label=\"%s\"];\n" edge.cfg_from.bb_id edge.cfg_to.bb_id (s_escape label)

		let dot_debug_syntax_edge ch bb se =
			let edge bb' label =
				Printf.fprintf ch "n%i -> n%i[style=\"dashed\",color=\"gray\",label=\"%s\"];\n" bb.bb_id bb'.bb_id label;
			in
			match se with
			| SESubBlock(bb_sub,bb_next) ->
				edge bb_sub "sub";
				edge bb_next "next";
			| SEIfThen(bb_then,bb_next) ->
				edge bb_then "then";
				edge bb_next "next"
			| SEIfThenElse(bb_then,bb_else,bb_next,_) ->
				edge bb_then "then";
				edge bb_else "else";
				edge bb_next "next";
			| SEWhile(bb_body,bb_next) ->
				edge bb_body "loop-body";
				edge bb_next "next";
			| SEMerge bb_next ->
				edge bb_next "merge"
			| SESwitch(bbl,bo,bb_next) ->
				List.iter (fun (el,bb) -> edge bb ("case " ^ (String.concat " | " (List.map s_expr_pretty el)))) bbl;
				(match bo with None -> () | Some bb -> edge bb "default");
				edge bb_next "next";
			| SETry(bb_try,bbl,bb_next) ->
				edge bb_try "try";
				List.iter (fun (_,bb_catch) -> edge bb_catch "catch") bbl;
				edge bb_next "next";
			| SEEnd ->
				()
			| SENone ->
				()

		let htmlescape s =
			let s = String.concat "&amp;" (ExtString.String.nsplit s "&") in
			let s = String.concat "&lt;" (ExtString.String.nsplit s "<") in
			let s = String.concat "&gt;" (ExtString.String.nsplit s ">") in
			s

		let generate_cfg_ssa ch g =
			Printf.fprintf ch "\tnode [shape=plaintext];\n";
			let expr_name b i = Printf.sprintf "e%s%i" (if b then "p" else "") i in
			Hashtbl.iter (fun _ bb ->
				Printf.fprintf ch "n%i[label=<<table BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">\n\t<tr><td port=\"in\" bgcolor=\"lightgray\">(%i) %s</td></tr>\n" bb.bb_id bb.bb_id (BasicBlock.s_block_kind bb.bb_kind);
				let s_expr b i e =
					Printf.fprintf ch "\t<tr><td port=\"%s\" align=\"left\">%s</td></tr>\n" (expr_name b i) (s_escape (htmlescape (s_expr_pretty e)))
				in
				DynArray.iteri (s_expr true) bb.bb_phi;
				DynArray.iteri (s_expr false) bb.bb_el;
				Printf.fprintf ch "\t<tr><td port=\"out\"></td></tr>\n</table>>];\n";
			) g.g_nodes;
			Graph.iter_edges g (fun edge ->
				Printf.fprintf ch "n%i:out -> n%i:in[label=\"%s\"];\n" edge.cfg_from.bb_id edge.cfg_to.bb_id (BasicBlock.s_cfg_edge_kind edge.cfg_kind)
			);
			DynArray.iter (fun vi ->
				begin try
					let (bb,is_phi,i) = match vi.vi_value with None -> raise Not_found | Some i -> i in
					let n1 = Printf.sprintf "n%i:%s" bb.bb_id (expr_name is_phi i) in
					List.iter (fun (bb',is_phi',i') ->
						if bb != bb' then begin (* intra-node edges look stupid in dot *)
							let n2 = Printf.sprintf "n%i:%s" bb'.bb_id (expr_name is_phi' i') in
							Printf.fprintf ch "%s -> %s[color=lightblue,constraint=false];\n" n1 n2;
						end
					) vi.vi_ssa_edges;
				with Not_found ->
					()
				end
			) g.g_var_infos

		let dot_debug ctx c cf =
			let g = ctx.graph in
			let start_graph ?(graph_config=[]) suffix =
				let ch = Codegen.create_file suffix [] ("dump" :: [Common.platform_name ctx.com.platform] @ (fst c.cl_path) @ [Printf.sprintf "%s.%s" (snd c.cl_path) cf.cf_name]) in
				Printf.fprintf ch "digraph graphname {\n";
				List.iter (fun s -> Printf.fprintf ch "%s;\n" s) graph_config;
				ch,(fun () ->
					Printf.fprintf ch "}\n";
					close_out ch
				)
			in
			let ch,f = start_graph "-cfg.dot" in
			Hashtbl.iter (fun _ bb -> dot_debug_node g ch [NILoopGroups;NIScopes;NIPhi;NIExpr] bb) g.g_nodes;
			Graph.iter_edges g (dot_debug_cfg_edge ch);
			f();
			let ch,f = start_graph "-cfg-ssa.dot" in
			generate_cfg_ssa ch g;
			f();
			let ch,f = start_graph "-dj.dot" in
			Hashtbl.iter (fun _ bb ->
				dot_debug_node g ch [] bb;
				List.iter (fun einc ->
					let bb' = einc.cfg_from in
					let style = if bb' == bb.bb_dominator then "solid" else "dashed" in
					Printf.fprintf ch "n%i -> n%i[style=\"%s\"];\n" bb'.bb_id bb.bb_id style;
				) bb.bb_incoming;
			) g.g_nodes;
			f();
			let ch,f = start_graph "-df.dot" in
			Hashtbl.iter (fun _ bb ->
				dot_debug_node g ch [NIVars] bb;
				List.iter (fun bb' -> Printf.fprintf ch "n%i -> n%i;\n" bb.bb_id bb'.bb_id) bb.bb_df;
			) g.g_nodes;
			f();
			let ch,f = start_graph "-dom.dot" in
			Hashtbl.iter (fun _ bb ->
				dot_debug_node g ch [NIVars] bb;
				List.iter (fun bb' -> Printf.fprintf ch "n%i -> n%i;\n" bb.bb_id bb'.bb_id) bb.bb_dominated;
			) g.g_nodes;
			f();
			let ch,f = start_graph "-syntax.dot" in
			Hashtbl.iter (fun _ bb ->
				dot_debug_node g ch [NIExpr] bb;
				dot_debug_syntax_edge ch bb bb.bb_syntax_edge
			) g.g_nodes;
			f();
			let ch,f = start_graph "-ssa-edges.dot" in
			let nodes = ref PMap.empty in
			let node_name bb is_phi i = Printf.sprintf "e%i_%b_%i" bb.bb_id is_phi i in
			let node_name2 bb is_phi i =
				let n = node_name bb is_phi i in
				nodes := PMap.add n true !nodes;
				n
			in
			DynArray.iter (fun vi ->
				begin try
					let (bb,is_phi,i) = match vi.vi_value with None -> raise Not_found | Some i -> i in
					let n1 = node_name2 bb is_phi i in
					List.iter (fun (bb',is_phi',i') ->
						let n2 = node_name2 bb' is_phi' i' in
						Printf.fprintf ch "%s -> %s;\n" n1 n2
					) vi.vi_ssa_edges
				with Not_found ->
					()
				end
			) g.g_var_infos;
			Hashtbl.iter (fun _ bb ->
				let f is_phi acc i e =
					let n = node_name bb is_phi i in
					(i + 1),if PMap.mem n !nodes then
						(n,s_expr_pretty e) :: acc
					else
						acc
				in
				let _,active_nodes = DynArray.fold_left (fun (i,acc) -> f true acc i) (0,[]) bb.bb_phi in
				let _,active_nodes = DynArray.fold_left (fun (i,acc) -> f false acc i) (0,active_nodes) bb.bb_el in
				if active_nodes <> [] then begin
					Printf.fprintf ch "subgraph cluster_%i {\n" bb.bb_id;
					Printf.fprintf ch "label=%i;\n" bb.bb_id;
					Printf.fprintf ch "style=filled;\n";
					Printf.fprintf ch "color=lightblue;\n";
					List.iter (fun (n,s) ->
						Printf.fprintf ch "%s[shape=box,label=\"%s\"];\n" n (s_escape s)
					) active_nodes;
					Printf.fprintf ch "}\n";
				end;
			) g.g_nodes;
			f()
	end

	module Purity = struct
		type purity =
			| Pure
			| NotPure
			| MaybePure

		type purity_node = {
			pn_field : tclass_field;
			mutable pn_purity : purity;
			mutable pn_dependents : purity_node list;
		}

		let node_lut = Hashtbl.create 0

		let get_field_id c cf = Printf.sprintf "%s.%s" (s_type_path c.cl_path) cf.cf_name

		let get_node c cf =
			try
				Hashtbl.find node_lut (get_field_id c cf)
			with Not_found ->
				let node = {
					pn_field = cf;
					pn_purity = MaybePure;
					pn_dependents = []
				} in
				Hashtbl.replace node_lut (get_field_id c cf) node;
				node

		let apply_to_field com is_ctor c cf =
			let node = get_node c cf in
			let rec taint node =
				if node.pn_purity <> NotPure then begin
					node.pn_purity <- NotPure;
					List.iter taint node.pn_dependents
				end
			in
			let taint_raise node =
				taint node;
				raise Exit;
			in
			let check_field c cf =
				let node' = get_node c cf in
				match node'.pn_purity with
					| Pure -> ()
					| NotPure -> taint_raise node;
					| MaybePure -> node'.pn_dependents <- node :: node'.pn_dependents
			in
			let rec check_write e1 =
				begin match e1.eexpr with
					| TLocal v ->
						() (* Writing to locals does not violate purity. *)
					| TField({eexpr = TConst TThis},_) when is_ctor ->
						() (* A constructor can write to its own fields without violating purity. *)
					| _ ->
						taint_raise node
				end
			and loop e = match e.eexpr with
				| TMeta((Meta.Pure,_,_),_) ->
					()
				| TThrow _ ->
					taint_raise node;
				| TBinop((OpAssign | OpAssignOp _),e1,e2) ->
					check_write e1;
					loop e2;
				| TUnop((Increment | Decrement),_,e1) ->
					check_write e1;
				| TCall({eexpr = TField(_,FStatic(c,cf))},el) ->
					List.iter loop el;
					check_field c cf;
				| TNew(c,_,el) ->
					List.iter loop el;
					begin match c.cl_constructor with
						| Some cf -> check_field c cf
						| None -> taint_raise node
					end
				| TCall({eexpr = TLocal v},el) when not (is_unbound_call_that_might_have_side_effects v el) ->
					List.iter loop el;
				| TCall _ ->
					taint_raise node
				| _ ->
					Type.iter loop e
			in
			match cf.cf_expr with
			| None ->
				taint node
			| Some e ->
				try
					if (Meta.has (Meta.Custom ":impure")) cf.cf_meta then taint_raise node;
					if is_pure c cf then raise Exit;
					loop e;
					node.pn_purity <- Pure;
				with Exit ->
					()

		let apply_to_class com c =
			List.iter (apply_to_field com false c) c.cl_ordered_fields;
			List.iter (apply_to_field com false c) c.cl_ordered_statics;
			(match c.cl_constructor with Some cf -> apply_to_field com true c cf | None -> ())

		let infer com =
			Hashtbl.clear node_lut;
			List.iter (fun mt -> match mt with
				| TClassDecl c -> apply_to_class com c
				| _ -> ()
			) com.types;
			Hashtbl.fold (fun _ node acc ->
				if node.pn_purity = Pure then begin
					node.pn_field.cf_meta <- (Meta.Pure,[],node.pn_field.cf_pos) :: node.pn_field.cf_meta;
					node.pn_field :: acc
				end else acc
			) node_lut [];
	end

	module Cleanup = struct
		let apply ctx e =
			let com = ctx.com in
			let if_or_op e e1 e2 e3 = match (Texpr.skip e1).eexpr,(Texpr.skip e3).eexpr with
				| TUnop(Not,Prefix,e1),TConst (TBool true) -> Optimizer.optimize_binop {e with eexpr = TBinop(OpBoolOr,e1,e2)} OpBoolOr e1 e2
				| _,TConst (TBool false) -> Optimizer.optimize_binop {e with eexpr = TBinop(OpBoolAnd,e1,e2)} OpBoolAnd e1 e2
				| _,TBlock [] -> {e with eexpr = TIf(e1,e2,None)}
				| _ -> match (Texpr.skip e2).eexpr with
					| TBlock [] when com.platform <> Cs ->
						let e1' = mk (TUnop(Not,Prefix,e1)) e1.etype e1.epos in
						let e1' = Optimizer.optimize_unop e1' Not Prefix e1 in
						{e with eexpr = TIf(e1',e3,None)}
					| _ ->
						{e with eexpr = TIf(e1,e2,Some e3)}
			in
			let rec loop e = match e.eexpr with
				| TIf(e1,e2,Some e3) ->
					let e1 = loop e1 in
					let e2 = loop e2 in
					let e3 = loop e3 in
					if_or_op e e1 e2 e3;
				| TBlock el ->
					let el = List.map (fun e ->
						let e = loop e in
						match e.eexpr with
						| TIf _ -> {e with etype = com.basic.tvoid}
						| _ -> e
					) el in
					{e with eexpr = TBlock el}
				| TWhile(e1,e2,NormalWhile) ->
					let e1 = loop e1 in
					let e2 = loop e2 in
					begin match e2.eexpr with
						| TBlock ({eexpr = TIf(e1,({eexpr = TBlock[{eexpr = TBreak}]} as eb),None)} :: el2) ->
							let e1 = Texpr.skip e1 in
							let e1 = match e1.eexpr with TUnop(_,_,e1) -> e1 | _ -> {e1 with eexpr = TUnop(Not,Prefix,e1)} in
							{e with eexpr = TWhile(e1,{eb with eexpr = TBlock el2},NormalWhile)}
						| TBlock el ->
							let rec loop2 el = match el with
								| {eexpr = TBreak | TContinue | TReturn _ | TThrow _} as e :: el ->
									[e]
								| e :: el ->
									e :: (loop2 el)
								| [] ->
									[]
							in
							let el = loop2 el in
							{e with eexpr = TWhile(e1,{e2 with eexpr = TBlock el},NormalWhile)}
						| _ ->
							{e with eexpr = TWhile(e1,e2,NormalWhile)}
					end
				| _ ->
					Type.map_expr loop e
			in
			loop e

		let rec reduce_control_flow ctx e =
			Type.map_expr (reduce_control_flow ctx) (Optimizer.reduce_control_flow ctx e)
	end

	module Run = struct
		open Config
		open Graph

		let with_timer s f =
			let timer = timer s in
			let r = f() in
			timer();
			r

		let there com config e =
			let e = with_timer "analyzer-filter-apply" (fun () -> TexprFilter.apply com e) in
			let ctx = with_timer "analyzer-from-texpr" (fun () -> TexprTransformer.from_texpr com config e) in
			ctx

		let back_again ctx =
			let e = with_timer "analyzer-to-texpr" (fun () -> TexprTransformer.to_texpr ctx) in
			DynArray.iter (fun vi ->
				vi.vi_var.v_extra <- vi.vi_extra;
			) ctx.graph.g_var_infos;
			let e = with_timer "analyzer-fusion" (fun () -> Fusion.apply ctx.com ctx.config e) in
			let e = with_timer "analyzer-cleanup" (fun () -> Cleanup.apply ctx e) in
			e

		let roundtrip com config e =
			let ctx = there com config e in
			back_again ctx

		let run_on_expr com config c cf e =
			let ctx = there com config e in
			if com.debug then Graph.check_integrity ctx.graph;
			if config.optimize && not ctx.has_unbound then begin
				if config.tail_call_elimination then with_timer "analyzer-tail-call-elimination" (fun () -> TCE.apply ctx c cf);
				with_timer "analyzer-ssa-apply" (fun () -> Ssa.apply ctx);
				if config.const_propagation then with_timer "analyzer-const-propagation" (fun () -> ConstPropagation.apply ctx);
				if config.copy_propagation then with_timer "analyzer-copy-propagation" (fun () -> CopyPropagation.apply ctx);
				if config.code_motion then with_timer "analyzer-code-motion" (fun () -> CodeMotion.apply ctx);
				with_timer "analyzer-local-dce" (fun () -> LocalDce.apply ctx);
			end;
			ctx,back_again ctx

		let run_on_field ctx config c cf = match cf.cf_expr with
			| Some e when not (is_ignored cf.cf_meta) && not (Codegen.is_removable_field ctx cf) ->
				let config = update_config_from_meta ctx.Typecore.com config cf.cf_meta in
				let actx,e = run_on_expr ctx.Typecore.com config c cf e in
				let e = Cleanup.reduce_control_flow ctx e in
				if config.dot_debug then Debug.dot_debug actx c cf;
				let e = if actx.is_real_function then
					e
				else begin
					(* Get rid of the wrapping function and its return expressions. *)
					let rec loop first e = match e.eexpr with
						| TReturn (Some e) -> e
						| TFunction tf when first -> loop false tf.tf_expr
						| TFunction _ -> e
						| _ -> Type.map_expr (loop first) e
					in
					loop true e
			end in
			cf.cf_expr <- Some e;
		| _ -> ()

	let run_on_class ctx config c =
		let config = update_config_from_meta ctx.Typecore.com config c.cl_meta in
		let process_field stat cf = match cf.cf_kind with
			| Var _ when not stat -> ()
			| _ -> run_on_field ctx config c cf
		in
		List.iter (process_field false) c.cl_ordered_fields;
		List.iter (process_field true) c.cl_ordered_statics;
		(match c.cl_constructor with
		| None -> ()
		| Some f -> process_field false f)

	let run_on_type ctx config t =
		match t with
		| TClassDecl c when (is_ignored c.cl_meta) -> ()
		| TClassDecl c -> run_on_class ctx config c
		| TEnumDecl _ -> ()
		| TTypeDecl _ -> ()
		| TAbstractDecl _ -> ()

	let run_on_types ctx types =
		let com = ctx.Typecore.com in
		let config = get_base_config com in
		let cfl = if config.optimize && config.purity_inference then Purity.infer com else [] in
		List.iter (run_on_type ctx config) types;
		List.iter (fun cf -> cf.cf_meta <- List.filter (fun (m,_,_) -> m <> Meta.Pure) cf.cf_meta) cfl
end