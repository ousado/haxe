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
open AnalyzerTexpr
open AnalyzerTypes

(* File organization:
	* analyzer.ml: The controlling file with all graph-based optimizations
	* analyzerConfig.ml: The general configuration which is used in multiple modules
	* analyzerTexpr.ml: Transformations and query functions on texpr, independent of graph/blocks
	* analyzerTexprTransformer.ml: Translation of texpr to graph/blocks
	* analyzerTypes.ml: Definition of graph, block and the analyzer context
*)

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
			let v' = alloc_var (v.v_name) v.v_type v.v_pos in
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
		Graph.infer_dominance_frontier ctx.graph;
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
				let e = get_texpr bb is_phi i in
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
			if not (List.exists (fun edge -> has_flag edge FlagExecutable) bb.bb_incoming) then bb.bb_dominator <- ctx.graph.Graph.g_unreachable;
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
						let v' = alloc_var ctx.temp_var_name v.v_type v.v_pos in
						declare_var ctx.graph v' bb_loop_pre;
						v'.v_meta <- [Meta.CompilerGenerated,[],p];
						v'
					end in
					let e = to_texpr lat in
					let e = mk (TVar(v',Some e)) ctx.com.basic.tvoid p in
					add_texpr bb_loop_pre e;
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
					let e = BasicBlock.get_texpr bb is_phi i in
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

module TCE = struct
	open BasicBlock
	open Graph

	type tce_mode =
		| TCEStrict
		| TCEMaybe
		| TCENo

	type tce_invocation =
		| ITCEStrict
		| ITCELocal
		| ITCETry

	let s_tce_mode = function
		| TCEStrict -> "TCEStrict"
		| TCEMaybe -> "TCEMaybe"
		| TCENo -> "TCENo"

	type 'a result =
		| RValue of 'a
		| RError of string

	type fdata_kind =
		| FKStatic of tclass * tclass_field
		| FKInstance of tclass * tclass_field
		| FKLocal

	type calldata = {
		cd_block : BasicBlock.t;
		cd_idx   : int;
		cd_expr  : texpr;
		mutable cd_intermediates : BasicBlock.t list;
		cd_fdata : fdata;
		cd_args  : texpr list;
		cd_this  : texpr option;
	}

	and fdata = {
		f_index        : int;                                   (* the index used for the switch *)
		f_tf           : tfunc;
		f_call_var_m   : (int,tvar) PMap.t;                     (* the local var used as tmp var to 'call' this function *)
		f_call_vars    : (tvar * tvar * tconstant option) list; (* list of argument * call_tmp_var * optional value *)
		f_bb_begin     : BasicBlock.t;                          (* relevant blocks *)
		f_bb_end       : BasicBlock.t;
		f_bb_decl      : BasicBlock.t option;
		mutable f_is_entry : bool;
		mutable f_kind     : fdata_kind;                        (* defaults to FKLocal, needs to be changed after *)
		mutable f_blocks   : BasicBlock.t list;                 (* all blocks that are initially pert of this function *)
		mutable f_mode     : tce_mode;							(* must become either TCEStrict or TCENo *)
		mutable f_rec_tail_calls : (int,calldata) PMap.t;       (* all recursive calls in tail position, indexed by block*)
		mutable f_rec_calls : calldata list;                    (* all recursive calls, potentially not in tail position *)
	(*	f_exclude   : bool;               (* exclude from transformation *)
		f_selfrec   : bool;               (* does it call itself? *)
		f_mutualrec : bool;               (* does it call others in the same group? *) *)
	}

	exception TCE_failed

	let mk_fdata f_index f_tf f_call_var_m f_call_vars f_bb_begin f_bb_end f_bb_decl f_kind =
		{ f_index=f_index;
		f_tf=f_tf;
		f_call_var_m=f_call_var_m;
		f_call_vars=f_call_vars;
		f_bb_begin=f_bb_begin;
		f_bb_end=f_bb_end;
		f_bb_decl=f_bb_decl;
		f_is_entry=false;
		f_kind=f_kind;
		f_blocks = [];
		f_rec_tail_calls = PMap.empty;
		f_rec_calls = [];
		f_mode = TCEMaybe;
	}

	type mctx = {
		mutable funcs_by_vid : (int, fdata) PMap.t;
		mutable funcs_by_idx : (int, fdata) PMap.t;
		mutable funcs_by_bbid: (int, fdata) PMap.t;
		mutable funcs_by_field : (int, fdata) PMap.t;
		mutable captured_vars : (int,tvar) PMap.t;
		mutable recursive_calls : (int,(BasicBlock.t * int * fdata * texpr list * texpr option)) PMap.t;
									   (* bb 		 * idx * fdata * args 		* `this`*)
		mutable group_blocks : BasicBlock.t list;   (* all blocks of a group of recursive functions *)
		mutable entry_func : fdata option;
		actx : analyzer_context
	}

	let debug = false

	let foldi f acc l =
		let rec loop i acc xs = (match xs with
				| [] -> acc
				| x :: xs -> let acc = f i acc x in loop (i+1) acc xs
			)
		in loop 0 acc l

	let dynarray_foldi f acc da =
		let len = DynArray.length da in
		let rec loop i acc =
			if i = len then acc
			else
				let acc = f i acc (DynArray.get da i) in
				loop (i+1) acc
		in loop 0 acc


	let dopsid s id = print_endline (Printf.sprintf "%s id: %d " s id)
	let p_s_id s id = if debug then dopsid s id

	(* TODO cleanup, migrate into Graph perhaps *)

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

	let fold_filter f acc xs = begin
		let rec loop acc xs2 xs = (match xs with
			| [] -> acc, (List.rev xs2)
			| x :: xs ->
				let (r,acc) = f acc x in
				if r then loop acc (x :: xs2) xs else loop acc xs2 xs
		) in loop acc [] xs
	end

	let fold_dom_tree_filter filter f acc bb =
		let rec loop acc bb =
			let acc = f acc bb in
			List.fold_left loop acc (List.filter filter bb.bb_dominated)
		in loop acc bb

	let fold_dom_tree_function bb_begin = begin
			fold_dom_tree_filter
			(fun bb -> match bb.bb_kind with BKFunctionBegin _ -> false | _ -> true )
			(fun acc bb ->  bb :: acc )
			[]
			bb_begin
		end

	let get_func_end_block bb_begin =  begin match (
			fold_dom_tree_filter
			(fun bb -> match bb.bb_kind with BKFunctionBegin _ -> false | _ -> true )
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
	let mk_func_maps mctx func_ids = begin
		let g = mctx.actx.graph in
		let f_ord = List.sort compare func_ids in
		let (bbm,idxm) = foldi ( fun idx (bbm,idxm) bb_id ->
			let (bb,t,pos,tf) = Hashtbl.find g.g_functions bb_id in
			let bb_end  = get_func_end_block bb in
			let bb_decl =
				let bb_decl = get_func_decl_block bb in
				if bb_decl.bb_id = g.g_root.bb_id then None else Some(bb_decl)
			in
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


	let p_dom_tree g nmap =
		let pblock bb = DynArray.iteri ( fun idx e ->
			print_endline (Printf.sprintf "    %d::%s " idx (s_expr_pretty e ))
		) bb.bb_el in
		let _ = fold_dom_tree g.g_root g.g_exit (fun m bb ->
			let _ = try let n = PMap.find bb.bb_id nmap in
					dopsid ("checking " ^ n) bb.bb_id;
					pblock bb;
				with Not_found ->
					dopsid (
						Printf.sprintf "checking unknown with dom %d  and kind %s \n  [%s] "
						bb.bb_dominator.bb_id
						(BasicBlock.s_block_kind bb.bb_kind)
						(String.concat "," (List.map (fun bb -> (string_of_int bb.bb_id)) bb.bb_dominated ));
					) bb.bb_id;
					pblock bb;
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

	let filter_cfg_goto ce = (match ce with {cfg_kind=CFGGoto} -> true | _-> false)
	let filter_cfg_gotos cfgs = List.filter filter_cfg_goto cfgs

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

	let transform mctx =
		let g = mctx.actx.graph in
		let tvoid = mctx.actx.com.basic.tvoid  in
		let tint = mctx.actx.com.basic.tint in
		let tbool = mctx.actx.com.basic.tbool in
		let define_var bb v value =
			declare_var g v bb;
			(*dopsid ("### defining var " ^ v.v_name) v.v_id;*)
			let e = mk (TVar( v, value)) tvoid null_pos in
			add_texpr bb e
		in

		let mk_local v = mk(TLocal v) v.v_type null_pos in
		let close_blocks l = List.iter (fun bb -> bb.bb_closed <- true ) l in
		let fdata_entry = Option.get mctx.entry_func in

		let bb_dom = fdata_entry.f_bb_begin in

		let enull = mk(TConst(TNull)) tvoid null_pos in

		(*p_dom_tree g PMap.empty;*)

		(* handle `this` - get type, rewrite expressions, declare *)
		let thisdata = begin
			let vthis = alloc_var ( Printf.sprintf  "_tce_this%d" fdata_entry.f_index ) tvoid in
			(match fdata_entry.f_kind with
				| FKInstance _ ->
					let rec loop e = (match e.eexpr with
						| TConst(TThis) ->
							vthis.v_type <- e.etype;
							mk_local vthis
						| _ -> Type.map_expr loop e
					) in
					iter_dom_tree g (fun bb ->
						dynarray_map loop bb.bb_el
					);
					Some ((mk_local vthis),vthis,loop)
				| _ -> None
			)
			end
		in

		(*   structure   *)
		let bb_setup = create_node g BKNormal tvoid null_pos in
		let bb_while = create_node g BKNormal tvoid null_pos in
		let bb_loophead = create_node g BKLoopHead  tvoid null_pos in
		let bb_switch = create_node g BKNormal bb_dom.bb_type null_pos in

		add_cfg_edge bb_setup bb_while CFGGoto;
		add_cfg_edge bb_while bb_loophead CFGGoto;
		add_cfg_edge bb_loophead bb_switch CFGGoto;

		set_syntax_edge bb_while (SEWhile(bb_loophead,bb_switch,g.g_unreachable));

		(* declare/define tmp call vars, captured vars and arguments, and maybe `this` outside the main loop in bb_setup  *)
		(match thisdata with
			| Some (ethis,vthis,_) ->
					define_var bb_setup vthis (Some(mk (TConst(TThis)) vthis.v_type null_pos ));
			|_ ->()
		);

		PMap.iter ( fun idx f ->
			List.iter ( fun (v,cv,co) ->
				if not f.f_is_entry then begin
				(*dopsid ("defining var " ^ v.v_name) f.f_bb_begin.bb_id;*)
				define_var bb_setup v None;
			end) f.f_call_vars;
		) mctx.funcs_by_idx;

 		PMap.iter ( fun id v ->
			(* exclude entry function arguments and the local functions themselves *)
			let is_fentry_argument = (PMap.exists v.v_id fdata_entry.f_call_var_m) in
			let is_tce_func_but_not_entry = (match find_func_by_vid mctx v.v_id with
				| Some fdata -> if not fdata.f_is_entry then true else false
				| _ -> false) in
			let exclude = is_fentry_argument || is_tce_func_but_not_entry in
			(*print_endline (Printf.sprintf "is entry call var: %B is tce_func_but_not_entry %B  %b | %d %s "
										is_fentry_argument is_tce_func_but_not_entry exclude v.v_id v.v_name); *)
			if not exclude then begin
				v.v_name <-  (Printf.sprintf "_tce_cap_%d_%s" v.v_id v.v_name); (* give it a horrible unique name *)
				define_var bb_setup v None
			end
		) mctx.captured_vars;

		(* hook up entry function begin block - only write after bb_cases are set up *)

		set_syntax_edge bb_setup (SEMerge bb_while);

		let rewrite_dom_edges = (fun () ->
				set_syntax_edge bb_dom (SEMerge bb_setup);
				add_cfg_edge bb_dom bb_setup CFGGoto;
		) in

		(* add while(true) *)
		let make_block_meta b =
			let e = mk (TConst (TInt (Int32.of_int b.bb_id))) tint b.bb_pos in
			wrap_meta ":block" e
		in
		let etrue = mk (TConst(TBool true)) tbool null_pos in
		let ewhile = mk  (TWhile(etrue,make_block_meta bb_switch,NormalWhile)) tvoid null_pos in
		add_texpr bb_while ewhile;

		(* switch branch *)
		let mk_int i =  (mk (TConst( TInt(Int32.of_int i)))  tint null_pos) in
		let tce_loop_var = alloc_var "_hx_tce_current_function" tint in
		define_var bb_setup tce_loop_var (Some (mk (TConst( TInt(Int32.of_int fdata_entry.f_index)))  tint null_pos));

		add_texpr bb_switch (wrap_meta ":cond-branch" (mk (TLocal(tce_loop_var)) tce_loop_var.v_type null_pos));

		let assign_var v evalue =
			let ev = mk (TLocal v) v.v_type null_pos in
			mk (TBinop(OpAssign,ev,evalue)) v.v_type null_pos
		in

		(* each case corresponds to one of the functions tce is being applied to *)
		let bb_cases = PMap.foldi ( fun idx fdata acc  -> (
			let bb_case = create_node g BKNormal bb_dom.bb_type null_pos in
			let bb_case_init = create_node g BKConditional tvoid null_pos in
			let te = mk (TConst (TInt (Int32.of_int idx))) t_dynamic null_pos in

			add_cfg_edge bb_switch bb_case_init (CFGCondBranch te);
			add_cfg_edge bb_case_init bb_case CFGGoto;
			set_syntax_edge bb_case_init (SEMerge bb_case);

			let transfer_statements bbf bbt tf =
				if PMap.exists bbf.bb_id  mctx.recursive_calls then begin
					let m = mctx.recursive_calls in (* a bit of a hack here, TODO *)
					let (bb,call_idx,fdata_callee,args,othis) = (PMap.find bbf.bb_id m) in
					mctx.recursive_calls <- PMap.add bb_case.bb_id (bb_case,call_idx,fdata_callee,args,othis) m;
				end else ();
				DynArray.iteri ( fun idx e ->
					DynArray.set bbf.bb_el idx enull;
					add_texpr bb_case e
				) bbf.bb_el;
			in

			let filter_func_cfges ce = (match ce with
				| {cfg_kind=CFGFunction;cfg_to=cfg_to} -> if (PMap.exists cfg_to.bb_id mctx.funcs_by_bbid) then false else true
				| _ -> true
			) in

			let transfer_edges bbf bbt tf =
				let cfges = List.filter filter_func_cfges bbf.bb_outgoing in
				bbf.bb_outgoing <- [];
				if not (bbf == bb_dom) then bbf.bb_incoming <- [];
				List.iter ( fun ce ->
					ce.cfg_to.bb_incoming <- List.filter
						( fun {cfg_from=cfg_from} -> not (cfg_from.bb_id = bbf.bb_id) ) ce.cfg_to.bb_incoming;
					add_cfg_edge bb_case ce.cfg_to ce.cfg_kind;
				) cfges;
				set_syntax_edge bb_case bbf.bb_syntax_edge
			in

			let rewrite_func_end_blocks bbf bbfend tf =
				(* all incoming edges of bfend need to be redirected to the end of the main function or
				* to the loop header *)

				let rcall_blocks = PMap.fold (fun cd acc -> cd.cd_block :: acc ) fdata.f_rec_tail_calls [] in

				PMap.iter ( fun bb_id cd ->
						(* 1. remove call *)
						DynArray.delete cd.cd_block.bb_el cd.cd_idx; (* set this to null, rather? *)
						let bb = cd.cd_block in
						let fdata_callee = cd.cd_fdata in
						let calldata_args = (List.combine fdata_callee.f_call_vars cd.cd_args) in
						let cvs = List.map (fun ((v,cv,co),evalue) ->
							let cv = alloc_var cv.v_name cv.v_type in
							define_var bb cv (Some evalue);
							cv;
						) calldata_args in
						List.iter (fun (((v,_,co),evalue),cv) ->
							let cv_value = mk_local cv in
							let e = assign_var v cv_value in
							add_texpr bb e;
						) (List.combine calldata_args cvs);
						(match (cd.cd_this,thisdata) with
							| Some(evalue),Some(ethis,vthis,f) ->
								add_texpr bb (assign_var vthis (f evalue))
							| _ -> ()
						);
						let e = assign_var tce_loop_var (mk_int fdata_callee.f_index) in
						add_texpr bb e;
						add_texpr bb (mk (TContinue) tvoid null_pos);

				) fdata.f_rec_tail_calls;

				let accounted_for = PMap.fold (fun cd m ->
					List.fold_left (fun m bb -> PMap.add bb.bb_id bb m) m cd.cd_intermediates) fdata.f_rec_tail_calls PMap.empty in

				(* we walk back from function-end, if we encounter an incoming CFGGoto edge that isn't in accounted_for
				 * it means that edge comes from not-a-tail-call - if we're in a Void function, we have to add a return
				 * because otherwise our loop will run forever
				 * However, since we can come across nodes with several incoming edges, we have to walk back until we've
				 * encountered all blocks containing the tail-calls themselves - only then we can be sure that there are
				 * no unaccounted for incoming cfg edges
				 * *)

				let is_void = function (* TODO use version in type.ml *)
						| TAbstract({a_path=[],"Void"},_) -> true
						| _ -> false
				in

				let from_blocks cfgs = List.map (fun {cfg_from=bb} -> bb) cfgs in
				let to_blocks cfgs = List.map (fun {cfg_to=bb} -> bb) cfgs in

				let cfg_disconnect bb_from bb_to = begin
					bb_from.bb_outgoing <- List.filter (fun ce -> not (ce.cfg_to.bb_id == bb_to.bb_id)) bb_from.bb_outgoing;
					bb_to.bb_incoming <- List.filter (fun ce -> not (ce.cfg_from.bb_id == bb_from.bb_id)) bb_to.bb_incoming;
				end in

				let cfg_disconnect_outgoing bb_from =
					List.iter (fun bb_to -> cfg_disconnect bb_from bb_to) (to_blocks bb_from.bb_outgoing) in
				let cfg_disconnect_incoming bb_to =
					List.iter (fun bb_from -> cfg_disconnect bb_from bb_to) (from_blocks bb_to.bb_incoming) in

				let rec walk_back bb acc_unaccounted =
					if PMap.exists bb.bb_id fdata.f_rec_tail_calls then
						acc_unaccounted
					else begin
						let inc = filter_cfg_gotos bb.bb_incoming in
						let acc_unaccounted = List.fold_left (fun acc_unaccounted bb_next ->
							if not (PMap.exists bb_next.bb_id accounted_for) then
								(bb,bb_next) :: acc_unaccounted
							else
								walk_back bb acc_unaccounted
						) acc_unaccounted (from_blocks inc) in acc_unaccounted
					end
				in
				let non_rcall_blocks = walk_back fdata.f_bb_end [] in
				let bb_exit = fdata_entry.f_bb_end in

				(* we completely disconnect the function end and remove intermediate nodes from the graph
				 * to avoid confusing dom inference before setting the necessary edges again *)
				let remove = PMap.foldi (fun k v m ->
					if not (PMap.exists k fdata.f_rec_tail_calls) then
						PMap.add k v m
					else m
				) accounted_for PMap.empty in
				PMap.iter ( fun id bb ->
					 cfg_disconnect_outgoing bb;
					 cfg_disconnect_incoming bb;
				) remove;

				if not fdata.f_is_entry then begin
					cfg_disconnect_outgoing fdata.f_bb_end;
					cfg_disconnect_incoming fdata.f_bb_end;
				end;

				let handle_rcall bb =
					cfg_disconnect bb fdata.f_bb_end;
					cfg_disconnect_outgoing bb;
					add_cfg_edge bb bb_loophead CFGGoto;
					add_cfg_edge bb bb_exit CFGMaybeThrow; (* this allows LocalDCE to find the block *)
				in
				List.iter handle_rcall rcall_blocks;

				let handle_non_rcall (bb_to,bb_non_rcall) =
					cfg_disconnect bb_non_rcall bb_to;
					let bb_next = if is_void fdata_entry.f_tf.tf_type then begin
						let bb = create_node g BKNormal tvoid null_pos in
						add_texpr bb (mk (TReturn None) tvoid null_pos);
						add_cfg_edge bb bb_exit CFGGoto;
						set_syntax_edge bb_non_rcall (SEMerge bb);
						bb
					end else
						bb_exit
					in
					add_cfg_edge bb_non_rcall bb_next CFGGoto
				in
				List.iter handle_non_rcall non_rcall_blocks

			in
			let (bbf,bbfend,tf) =  (fdata.f_bb_begin,fdata.f_bb_end,fdata.f_tf) in

			transfer_statements bbf bbfend tf;
			transfer_edges bbf bbfend tf;
			rewrite_func_end_blocks bbf bbfend tf;
			bb_case.bb_closed <- true;
			(bb_case_init,te) :: acc
		)) mctx.funcs_by_idx [] in


		let bb_cases_data = bb_cases in
		let bb_cases = List.map (fun (b,_) -> b) bb_cases_data in


		let all_blocks = [bb_setup;bb_while;bb_loophead;bb_switch] in
		let bb_names = ["setup";"while";"loophead";"switch"] in
		let nmap = List.fold_left (fun m (bb,n) -> PMap.add bb.bb_id n m) PMap.empty (List.combine all_blocks bb_names) in
		let _ = List.fold_left (fun m bb -> PMap.add bb.bb_id "bb_case" m) nmap bb_cases in

		let switchcases = List.map (fun (bb_case,te) -> [te],bb_case ) (List.rev bb_cases_data) in
		set_syntax_edge bb_switch (SESwitch(switchcases,None,g.g_unreachable));

		rewrite_dom_edges ();

		check_integrity g;
		infer_immediate_dominators g;
		(*check_integrity g;*)

		(*p_dom_tree g nmap;*)

		close_blocks [bb_setup;bb_while;bb_loophead;bb_switch];
		close_blocks bb_cases;

		(* clean up - turn all captured var definitions into assignments
		 * remove all eliminated functions *)
		if true then begin
		iter_dom_tree g (fun bb ->
			dynarray_map (fun e -> (match e.eexpr with
				| TVar(v,_)
				| TBinop(OpAssign,{eexpr=TLocal v},_) -> (match find_func_by_vid mctx v.v_id with
					| Some fdata -> if not fdata.f_is_entry then enull else e
					| _ -> e)
				| _ -> e
			)) bb.bb_el;
			(* exclude bb_setup here *)
			let exclude = bb.bb_id = bb_setup.bb_id in
			dynarray_map (fun e -> (match e.eexpr with
				| TVar(v,eo) ->
					if not exclude && (PMap.exists v.v_id mctx.captured_vars) then
						Option.map_default ( fun evalue -> assign_var v evalue) enull eo
					else e
				| _ -> e
			) ) bb.bb_el;
		);
		(*p_dom_tree g nmap;*)
		end;
		()

	let is_tce_call mctx e =
		(match e.eexpr with
		| TCall({eexpr=TLocal v},args) ->
				if is_unbound v then None else begin
				Option.map (fun fdata -> fdata,args,None ) (find_func_by_vid mctx v.v_id) end
		| TCall({eexpr= TField(ethis, FInstance(c,_,cf))},args) ->
				Option.map (fun fdata -> fdata,args, (Some ethis) ) (find_func_by_field mctx c cf)
		| TCall({eexpr= TField(_ , ( FStatic(c,cf)) )},args ) ->
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


	let edge_to_exit bb =
		(match bb.bb_outgoing with
			| [{cfg_to={bb_kind = BKFunctionEnd }}] -> true
			| _ -> false )

	let find_rec_calls mctx fdata =
		List.iter ( fun bb ->
			DynArray.iteri( fun idx te ->
				let callo = (has_tce_call mctx te) in
				fdata.f_rec_calls <- (match callo with
					| Some (fdata_callee,args,othis) ->
						{	cd_block=bb;
							cd_idx=idx;
							cd_expr=te;
							cd_intermediates=[];
							cd_fdata=fdata_callee;
							cd_args=args;
							cd_this=othis
						} :: fdata.f_rec_calls
					| _ -> fdata.f_rec_calls )
			) bb.bb_el
		) fdata.f_blocks


	let rec list_until_exit bb idx acc_el acc_blocks =
		let len = DynArray.length bb.bb_el in
		let rec loop idx acc acc_blocks =
			if idx < len then
				loop (idx+1) ((bb,idx,(DynArray.get bb.bb_el idx)) :: acc_el) acc_blocks
			else (match filter_cfg_gotos bb.bb_outgoing with (* only one outgoing cfg goto is allowed here *)
				| [{cfg_to={bb_kind=BKFunctionEnd}}] ->
						Some (acc_el,acc_blocks)
				| [{cfg_to=bb_next}] ->
						list_until_exit bb_next 0 acc_el (bb :: acc_blocks)
				| _ -> None) (* this is indicates that the call is in an invalid position *)
		in loop idx acc_el acc_blocks

	let check_rec_call mctx fdata invalid_acc cd =
		let add_valid_tail_call cd =
			fdata.f_rec_tail_calls <- PMap.add cd.cd_block.bb_id cd fdata.f_rec_tail_calls
		in
		let bb_el = cd.cd_block.bb_el in
		let len = DynArray.length bb_el in
		if cd.cd_idx = len-1 && edge_to_exit cd.cd_block then begin
			add_valid_tail_call cd;
			invalid_acc
		end else begin match (list_until_exit cd.cd_block (len-1) [] []) with
			| Some (acc_el,acc_blocks) ->
					let el = List.filter (* the only expressions allowed here are void returns *)
								( fun (_,_,e) -> match e.eexpr with TReturn None -> false | _ -> true ) acc_el in
					if el != [] then
						cd :: invalid_acc
					else begin
						cd.cd_intermediates <- acc_blocks;
						add_valid_tail_call cd;
						invalid_acc
					end
			| None -> cd :: invalid_acc
		end

	let check_rec_calls mctx error_with_warnings =
		let check_function fdata invalid =
			let invalid_calls = List.fold_left (check_rec_call mctx fdata) [] fdata.f_rec_calls in
			invalid_calls :: invalid
		in
		let invalid_calls = PMap.fold check_function mctx.funcs_by_bbid [] in
		match invalid_calls with
		| [[]] -> ()
		| _ ->
			if error_with_warnings then begin
			let invalid_calls = List.flatten invalid_calls in
			List.iter (fun cd -> mctx.actx.com.warning "call not in tail position" cd.cd_expr.epos ) (List.rev invalid_calls);
			error "Analyzer TCE: Some calls are not in tail position - see above warnings for more." null_pos;
			end else
				raise TCE_failed


	let add_cap m v = if v.v_capture then PMap.add v.v_id v m else m

	let add_caps_e m e = (match e.eexpr with
		| TVar(v,_) -> add_cap m v
		| _ -> m )

	let add_caps_f m tf = List.fold_left ( fun m (v,co) -> add_cap m v ) m tf.tf_args

	let find_local_func ctx bb idx tce_mode e = (match e.eexpr with
		| TVar (v, Some({eexpr=TCall({eexpr = TConst (TString "fun")},[{eexpr = TConst (TInt i32)}])}))
		| TBinop (OpAssign,( {eexpr=TLocal v}),
			{eexpr=TCall({eexpr = TConst (TString "fun")},[{eexpr = TConst (TInt i32)}])}) ->
			begin
				let bb_func_id = (Int32.to_int i32) in
				let vars = if not (DynArray.length bb.bb_el > (idx+1)) then [v] else
					(match (DynArray.get bb.bb_el (idx+1)).eexpr with
					| TVar(vleft,Some({eexpr=TLocal v2})) when (v2.v_id = v.v_id) -> [v;vleft]
					| _ -> [v])
				in
				(* print_endline (Printf.sprintf " found function %s vidx %s for function "
				 * v.v_name (String.concat "," (List.map (fun v -> string_of_int v.v_id) vars) ));*)
				let get_meta m = (match m with
					| (Meta.Analyzer,[(EConst(Ident "tce_strict"),_)],_) -> Some TCEStrict
					| (Meta.Analyzer,[(EConst(Ident "no_tce"),_)],_) -> Some TCENo
					| (Meta.Analyzer,[(EConst(Ident s),_)],_) ->
						if ExtString.String.exists s "tce" then
							error "unknown @:analyzer(*tce*) metadata" e.epos
						else None
					| _ -> None
				) in
				let mode = List.fold_left (fun mode v ->
					List.fold_left (fun mode meta -> (match (mode,(get_meta meta)) with
					| (Some m),_ -> Some m
					| None,Some m -> Some m
					| _ -> mode )
				) mode v.v_meta ) None vars
				in
				Some (bb_func_id, (Option.map_default (fun m -> m) TCEMaybe mode),vars)
			end
		| _ -> None )


	let apply ctx c cf tce_invocation = begin
		let g = ctx.graph in
		let bb_entry = (match g.g_root.bb_outgoing with
		    | [{cfg_to={bb_kind=BKFunctionBegin _} as bb}] -> bb
			| _ -> assert false (* really?? *)
		) in
		let (tce_mode,raise_on_error) = (match tce_invocation with
			| ITCELocal -> TCEMaybe,false
			| ITCEStrict -> TCEStrict,false
			| ITCETry -> TCEStrict,true
		) in
		(*p_dom_tree g PMap.empty;*)
		(* get all blocks that belong to one function, excluding sub functions, collect sub function entry blocks separately *)
		let rec loop_scope (funcs,blocks) bb = (match bb.bb_dominated with
			| [] -> funcs,blocks
			| _  ->
				let (nfuncs,nblocks) = List.partition (fun bb -> (match bb.bb_kind with
					| BKFunctionBegin _ -> true
					| _ -> false )
				) bb.bb_dominated in
				List.fold_left loop_scope ((funcs @ nfuncs),(blocks @ nblocks)) nblocks )
		in
		let rec loop_func parent fqueue acc =
			let (funcs,blocks) = loop_scope ([],[]) parent in
			let acc = (parent,funcs,blocks) :: acc in
			let fqueue = fqueue @ funcs in
			(match fqueue with
				| [] -> acc
				| func :: fqueue -> loop_func func fqueue acc
			)
		in
		(* flat is a list of tuples with a fbegin block * fbegin blocks of direct sub functions * contained blocks *)
		let flat = loop_func bb_entry [] [] in
		let s_bbids bbs = (String.concat "," (List.map ( fun bb -> string_of_int bb.bb_id ) bbs )) in

		let mode_vars_m = PMap.empty in (* mode_vars_m is a (bb_function_begin.bb_id, (tce_mode * tvar list)) PMap - the tvars are the locals this function is assigned to *)
		let (mode_vars_m,fdata_m) = List.fold_left (fun (mode_vars_m, acc_m) (p,fs,bs) ->
			(*print_endline (Printf.sprintf "p: %d cs: %s blocks: [%s] " p.bb_id (s_bbids fs) (s_bbids bs) );*)
			let caps_m = PMap.empty in
			let tf = match p with {bb_kind=BKFunctionBegin tf} -> tf | _ -> assert false in
			let caps_m = add_caps_f caps_m tf in
			let (caps_m,mode_vars_m) = List.fold_left ( fun (caps_m,mode_vars_m) bb ->
				dynarray_foldi (fun idx (caps_m,mode_vars_m) e ->
					let caps_m = add_caps_e caps_m e in
					let opt = find_local_func ctx bb idx TCEMaybe e in
					let mode_vars_m = Option.map_default
						(fun (bbid,mode,vars) -> PMap.add bbid (mode,vars) mode_vars_m) mode_vars_m opt
					in
					caps_m,mode_vars_m
				) (caps_m,mode_vars_m) bb.bb_el
			) (caps_m,mode_vars_m) (p :: bs) in
			(mode_vars_m, PMap.add p.bb_id (p,fs,bs,caps_m) acc_m)
		) (mode_vars_m,PMap.empty) flat in

		(* build groups of tce functions *)
		let get_mode bb = let (mode,_) = try
			PMap.find bb.bb_id mode_vars_m with Not_found ->
				if raise_on_error then
					raise TCE_failed
				else
					error ( "Analyzer/TCE module internal error: child function not found: " ^ s_bbids [bb]) bb.bb_pos
			in mode
		in
		let get_fdata bb = (PMap.find bb.bb_id fdata_m) in

		let group_tce_functions bb tce_mode group_maps =
			let rec loop (p,fs,_,_) pmode group_maps =
				let group_maps= List.fold_left ( fun maps f ->
					let fmode = get_mode f in
					let maps,fmode = (match (pmode,fmode) with
						| TCEMaybe,(TCEMaybe|TCENo) ->
							maps,fmode 						(* we're not in tce mode (yet) *)
						| TCEMaybe,TCEStrict -> 			(* we enter tce mode - create a new map for this group, add it to the list *)
							((PMap.add f.bb_id f PMap.empty) :: maps),TCEStrict
						| TCEStrict,TCENo ->
							maps,TCENo              		(* no_tce is declared - don't include f *)
						| TCEStrict,(TCEMaybe|TCEStrict) -> (* we're in strict mode, so there must be a map in the list *)
							(match maps with
								| [] -> assert false
								| m :: xs -> ((PMap.add f.bb_id f m) :: xs),TCEStrict)
						| TCENo,(TCEMaybe|TCENo) ->
							maps,TCENo  					(* inside a no_tce function, no tce is allowed anymore *)
						| TCENo,TCEStrict ->
							error "inside a @:no_tce function, no inner @:tce_strict functions are allowed" f.bb_pos
					) in loop (get_fdata f) fmode maps 		(* exhaust inner functions *)
				) group_maps fs
				in group_maps
			in loop (get_fdata bb) tce_mode group_maps
		in
		let group_maps = (match tce_mode with TCEStrict -> [PMap.add bb_entry.bb_id bb_entry PMap.empty] | _ -> [] ) in
		let group_maps = group_tce_functions bb_entry tce_mode group_maps in

		(*List.iter (fun m ->
			(print_endline ( "[" ^ (s_bbids (PMap.fold (fun f acc -> f :: acc ) m [])) ^ "]" ))) group_maps;
		print_endline "^^^^^^^^^^^^^ group maps ^^^^^^^^^^^^^^^^^"; *)

		List.iter (fun m ->
			let mctx = {
				funcs_by_vid = PMap.empty;
				funcs_by_idx = PMap.empty;
				funcs_by_bbid= PMap.empty;
				funcs_by_field = PMap.empty;
				captured_vars =  PMap.empty;
				recursive_calls = PMap.empty;
				group_blocks = [];
				entry_func = None;
				actx = ctx;
			} in

			let func_ids = List.sort compare (PMap.fold (fun f acc -> f.bb_id :: acc ) m []) in
			mk_func_maps mctx func_ids;

			(* the lowest func block id is the entry point *)
			let fdata_entry = PMap.find (List.hd func_ids) mctx.funcs_by_bbid in
			(*dopsid "entry func id: " fdata_entry.f_bb_begin.bb_id;*)
			fdata_entry.f_is_entry <- true;
			mctx.entry_func <- Some(fdata_entry);

			let group_blocks = PMap.fold ( fun f acc ->
				let (p,fs,bs,caps_m) = get_fdata f in
				let blocks = (p :: bs) in
				let fdata = PMap.find p.bb_id mctx.funcs_by_bbid in
				fdata.f_blocks <- blocks;
				PMap.iter ( fun id v -> mctx.captured_vars <- PMap.add id v mctx.captured_vars ) caps_m;
				(match tce_mode with
					| TCEStrict when p.bb_id == bb_entry.bb_id ->
						add_func_by_field mctx c cf p.bb_id true;
					| _ -> ());
				(try
					let (mode,vars) = PMap.find p.bb_id mode_vars_m in
					List.iter ( fun v -> add_func_by_vid mctx v.v_id p.bb_id ) vars;
				with
					Not_found -> ());
				find_rec_calls mctx fdata;
				check_rec_calls mctx (not raise_on_error); (* TODO check tce_mode for try_and_bail *)
				blocks :: acc
			) m [] in
			mctx.group_blocks <- (List.flatten group_blocks);
			transform mctx;
		) group_maps
	end
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
	open AnalyzerConfig

	let rec has_side_effect e =
		let rec loop e =
			match e.eexpr with
			| TConst _ | TLocal _ | TTypeExpr _ | TFunction _ -> ()
			| TCall ({ eexpr = TField(_,FStatic({ cl_path = ([],"Std") },{ cf_name = "string" })) },args) -> Type.iter loop e
			| TCall ({eexpr = TField(_,FEnum _)},_) -> Type.iter loop e
			| TCall ({eexpr = TConst (TString ("phi" | "fun"))},_) -> ()
			| TCall({eexpr = TField(e1,fa)},el) -> Optimizer.field_call_has_side_effect loop e1 fa el
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
		let bb_marked = ref [] in
		let rec mark bb =
			bb_marked := bb :: !bb_marked;
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
		List.iter (fun bb ->
			dynarray_map sweep bb.bb_el
		) !bb_marked;
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
			| BKFunctionBegin _ -> "<function-begin>\n"
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
		| SEWhile(bb_head,bb_body,bb_next) ->
			edge bb_head "loop-head";
			edge bb_body "loop-body";
			edge bb_next "next";
		| SEMerge bb_next ->
			edge bb_next "merge"
		| SESwitch(bbl,bo,bb_next) ->
			List.iter (fun (el,bb) -> edge bb ("case " ^ (String.concat " | " (List.map s_expr_pretty el)))) bbl;
			(match bo with None -> () | Some bb -> edge bb "default");
			edge bb_next "next";
		| SETry(bb_try,_,bbl,bb_next) ->
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
		List.iter (fun bb ->
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

	let get_dump_path ctx c cf =
		"dump" :: [Common.platform_name ctx.com.platform] @ (fst c.cl_path) @ [Printf.sprintf "%s.%s" (snd c.cl_path) cf.cf_name]

	let dot_debug ctx c cf =
		let g = ctx.graph in
		let start_graph ?(graph_config=[]) suffix =
			let ch = Codegen.Dump.create_file suffix [] (get_dump_path ctx c cf) in
			Printf.fprintf ch "digraph graphname {\n";
			List.iter (fun s -> Printf.fprintf ch "%s;\n" s) graph_config;
			ch,(fun () ->
				Printf.fprintf ch "}\n";
				close_out ch
			)
		in
		let ch,f = start_graph "-cfg.dot" in
		List.iter (fun bb -> dot_debug_node g ch [NILoopGroups;NIScopes;NIPhi;NIExpr] bb) g.g_nodes;
		Graph.iter_edges g (dot_debug_cfg_edge ch);
		f();
		let ch,f = start_graph "-cfg-ssa.dot" in
		generate_cfg_ssa ch g;
		f();
		let ch,f = start_graph "-dj.dot" in
		List.iter (fun bb ->
			dot_debug_node g ch [] bb;
			List.iter (fun einc ->
				let bb' = einc.cfg_from in
				let style = if bb' == bb.bb_dominator then "solid" else "dashed" in
				Printf.fprintf ch "n%i -> n%i[style=\"%s\"];\n" bb'.bb_id bb.bb_id style;
			) bb.bb_incoming;
		) g.g_nodes;
		f();
		let ch,f = start_graph "-df.dot" in
		List.iter (fun bb ->
			dot_debug_node g ch [NIVars] bb;
			List.iter (fun bb' -> Printf.fprintf ch "n%i -> n%i;\n" bb.bb_id bb'.bb_id) bb.bb_df;
		) g.g_nodes;
		f();
		let ch,f = start_graph "-dom.dot" in
		List.iter (fun bb ->
			dot_debug_node g ch [NIVars] bb;
			List.iter (fun bb' -> Printf.fprintf ch "n%i -> n%i;\n" bb.bb_id bb'.bb_id) bb.bb_dominated;
		) g.g_nodes;
		f();
		let ch,f = start_graph "-syntax.dot" in
		List.iter (fun bb ->
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
		List.iter (fun bb ->
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

module Run = struct
	open AnalyzerConfig
	open Graph

	let with_timer s f =
		let timer = timer s in
		let r = f() in
		timer();
		r

	let create_analyzer_context com config e =
		let g = Graph.create e.etype e.epos in
		let ctx = {
			com = com;
			config = config;
			graph = g;
			(* For CPP we want to use variable names which are "probably" not used by users in order to
			   avoid problems with the debugger, see https://github.com/HaxeFoundation/hxcpp/issues/365 *)
			temp_var_name = (match com.platform with Cpp -> "_hx_tmp" | _ -> "tmp");
			entry = g.g_unreachable;
			has_unbound = false;
			loop_counter = 0;
			loop_stack = [];
			debug_exprs = [];
		} in
		ctx

	let add_debug_expr ctx s e =
		ctx.debug_exprs <- (s,e) :: ctx.debug_exprs

	let there actx e =
		if actx.com.debug then add_debug_expr actx "initial" e;
		let e = with_timer "analyzer-filter-apply" (fun () -> TexprFilter.apply actx.com e) in
		if actx.com.debug then add_debug_expr actx "after filter-apply" e;
		let tf,is_real_function = match e.eexpr with
			| TFunction tf ->
				tf,true
			| _ ->
				(* Wrap expression in a function so we don't have to treat it as a special case throughout. *)
				let e = mk (TReturn (Some e)) t_dynamic e.epos in
				let tf = { tf_args = []; tf_type = e.etype; tf_expr = e; } in
				tf,false
		in
		with_timer "analyzer-from-texpr" (fun () -> AnalyzerTexprTransformer.from_tfunction actx tf e.etype e.epos);
		is_real_function

	let back_again actx is_real_function =
		let e = with_timer "analyzer-to-texpr" (fun () -> AnalyzerTexprTransformer.to_texpr actx) in
		if actx.com.debug then add_debug_expr actx "after to-texpr" e;
		DynArray.iter (fun vi ->
			vi.vi_var.v_extra <- vi.vi_extra;
		) actx.graph.g_var_infos;
		let e = with_timer "analyzer-fusion" (fun () -> Fusion.apply actx.com actx.config e) in
		if actx.com.debug then add_debug_expr actx "after fusion" e;
		let e = with_timer "analyzer-cleanup" (fun () -> Cleanup.apply actx.com e) in
		if actx.com.debug then add_debug_expr actx "after to-cleanup" e;
		let e = if is_real_function then
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
		e

	let run_on_expr actx cfo e =
		let is_real_function = there actx e in
		Graph.infer_immediate_dominators actx.graph;
		begin match cfo with
			| Some (c,cf)  ->
				if actx.config.tail_call_elimination && actx.config.tce_local then
					error "Only one of tce_strict and tce_local is allowed on a field" cf.cf_pos
				else if actx.config.tail_call_elimination then TCE.apply actx c cf TCE.ITCEStrict
				else if actx.config.tce_local then TCE.apply actx c cf TCE.ITCELocal
				else if (Common.raw_defined actx.com "TCE") then (try TCE.apply actx c cf TCE.ITCETry with TCE.TCE_failed -> ())
			| _ -> ()
		end;
		Graph.infer_scopes actx.graph;
		Graph.infer_var_writes actx.graph;
		if actx.com.debug then Graph.check_integrity actx.graph;
		if actx.config.optimize && not actx.has_unbound then begin
			with_timer "analyzer-ssa-apply" (fun () -> Ssa.apply actx);
			if actx.config.const_propagation then with_timer "analyzer-const-propagation" (fun () -> ConstPropagation.apply actx);
			if actx.config.copy_propagation then with_timer "analyzer-copy-propagation" (fun () -> CopyPropagation.apply actx);
			if actx.config.code_motion then with_timer "analyzer-code-motion" (fun () -> CodeMotion.apply actx);
			with_timer "analyzer-local-dce" (fun () -> LocalDce.apply actx);
		end;
		back_again actx is_real_function

	let run_on_field ctx config c cf = match cf.cf_expr with
		| Some e when not (is_ignored cf.cf_meta) && not (Codegen.is_removable_field ctx cf) ->
			let captured_vars = Codegen.VarCapturing.collect_captured_vars e in
			let config = update_config_from_meta ctx.Typecore.com config cf.cf_meta in
			let actx = create_analyzer_context ctx.Typecore.com config e in
			let debug() =
				prerr_endline (Printf.sprintf "While analyzing %s.%s" (s_type_path c.cl_path) cf.cf_name);
				List.iter (fun (s,e) ->
					prerr_endline (Printf.sprintf "<%s>" s);
					prerr_endline (Type.s_expr_pretty true "" (s_type (print_context())) e);
					prerr_endline (Printf.sprintf "</%s>" s);
				) (List.rev actx.debug_exprs);
				Debug.dot_debug actx c cf;
				prerr_endline (Printf.sprintf "dot graph written to %s" (String.concat "/" (Debug.get_dump_path actx c cf)));
			in
			let e = try
				run_on_expr actx (Some(c,cf)) e
			with
			| Error _ | Abort _ as exc ->
				raise exc
			| exc ->
				debug();
				raise exc
			in
			let e = Cleanup.reduce_control_flow ctx e in
			begin match config.debug_kind with
				| DebugNone -> ()
				| DebugDot -> Debug.dot_debug actx c cf;
				| DebugFull -> debug()
			end;
			let e = Codegen.VarCapturing.apply_captured_vars ctx.Typecore.com captured_vars e in
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
		begin match c.cl_constructor with
			| None -> ()
			| Some f -> process_field false f;
		end;
		begin match c.cl_init with
			| None ->
				()
			| Some e ->
				let tf = { tf_args = []; tf_type = e.etype; tf_expr = e; } in
				let e = mk (TFunction tf) (tfun [] e.etype) e.epos in
				let actx = create_analyzer_context ctx.Typecore.com {config with optimize = false} e in
				let e = run_on_expr actx None e in
				let e = match e.eexpr with
					| TFunction tf -> tf.tf_expr
					| _ -> assert false
				in
				let e = Codegen.VarCapturing.captured_vars ctx.Typecore.com e in
				c.cl_init <- Some e
		end

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
;;
Typecore.analyzer_run_on_expr_ref := (fun com e ->
	let actx = Run.create_analyzer_context com (AnalyzerConfig.get_base_config com) e in
	Run.run_on_expr actx None e
)

