open Il.Ast
open Util.Source

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
type agda_env = {
  mutable tf_set : StringSet.t;
  mutable il_env : Il.Env.t;
  mutable proj_set : StringSet.t;
  mutable wf_lemma_set : StringSet.t;
  mutable typ_to_wf_map : text StringMap.t;
  (* types needing Inhabited / HasEq *)
  mutable needed_inh : StringSet.t;
  mutable needed_eq : StringSet.t;
  (* per-fn type params needing HasEq / Inhabited *)
  mutable fun_eq_needs : StringSet.t StringMap.t;
  mutable fun_inh_needs : StringSet.t StringMap.t;
  (* types whose bool eq can't be generated, closed over containers *)
  mutable eq_skip : StringSet.t;
  (* ids of mutual group, eq calls siblings directly for structural recursion *)
  mutable cur_group : StringSet.t;
  mutable eq_helpers : StringSet.t
}

let new_env () = {
  tf_set = StringSet.empty;
  il_env = Il.Env.empty;
  proj_set = StringSet.empty;
  wf_lemma_set = StringSet.empty;
  typ_to_wf_map = StringMap.empty;
  needed_inh = StringSet.empty;
  needed_eq = StringSet.empty;
  fun_eq_needs = StringMap.empty;
  fun_inh_needs = StringMap.empty;
  eq_skip = StringSet.empty;
  cur_group = StringSet.empty;
  eq_helpers = StringSet.empty
}

let iter_prem_rels_list = ["Forall"; "Forall₂"; "Forall₃"]
let iter_exp_lst_funcs = ["map"; "zipWith"; "zipWith₃"]
let sup_iter_prem_rels_list = ["Foralli"]
let iter_exp_opt_funcs = ["mapMaybe"; "maybeZipWith"; "maybeZipWith₃"]
let error at msg = Util.Error.error at "Agda translation" msg

(* reduce type to head name, tolerate failure *)
let reduce_typ_safe env t = try Il.Eval.reduce_typ env t with _ -> t

let env_ref = ref (new_env ())

let is_let p =
  match p.it with
  | LetPr _ -> true
  | _ -> false

let rec is_type_family t =
  match t.it with
  | VarT (id, _) -> StringSet.mem id.it !env_ref.tf_set
  | IterT (t', _) -> is_type_family t'
  | TupT typs -> List.exists (fun (_, t') -> is_type_family t') typs
  | _ -> false

let is_type_family_param p =
  match p.it with
  | ExpP (_, t) -> is_type_family t
  | _ -> false

type exptype =
  | LHS
  | RHS

let var_prefix = "var-"

(* agda keywords + preamble ids, clashes get prime suffix *)
let keywords =
  ["abstract"; "coinductive"; "constructor"; "data"; "do"; "eta-equality";
  "field"; "forall"; "hiding"; "import"; "in"; "inductive"; "infix"; "infixl";
  "infixr"; "instance"; "interleaved"; "let"; "macro"; "module"; "mutual";
  "no-eta-equality"; "opaque"; "open"; "overlap"; "pattern"; "postulate";
  "primitive"; "private"; "public"; "quote"; "quoteTerm"; "record"; "renaming";
  "rewrite"; "syntax"; "tactic"; "unfolding"; "unquote"; "unquoteDecl";
  "unquoteDef"; "using"; "variable"; "where"; "with";
  "if"; "then"; "else";
  (* imported / preamble *)
  "true"; "false"; "not"; "zero"; "suc"; "tt"; "⊤"; "Bool"; "ℕ"; "String";
  "List"; "Maybe"; "nothing"; "just"; "mapMaybe"; "maybeZipWith"; "fromMaybe";
  "any"; "length"; "replicate"; "take"; "drop"; "zip"; "zipWith"; "zipWith₃";
  "maybeZipWith₃"; "map"; "proj₁"; "proj₂"; "×"; "⊎"; "refl"; "here"; "there";
  "upTo"; "mkseq"; "unsnoc-cons"; "as"; "slice"; "slice-update"; "modify"; "unwrap!"; "coerce";
  "Coerce"; "HasAppend"; "append"; "is-true"; "Forall"; "Forall₂"; "Forall₃";
  "Foralli"; "holds-upto"; "All"; "Pointwise"; "Set"; "Prop"; "Level"; "⊥"; "Inhabited";
  "default-val"; "HasEq"; "eqString"; "eq-List-fun"; "eq-Maybe-fun";
  "maybe-append"]
  |> StringSet.of_list

let remove_iter_from_type t =
  match t.it with
  | IterT (t', _) -> t'
  | _ -> t

let string_of_list_prefix prefix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls)

let string_of_list_suffix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> String.concat delim (List.map str_func ls) ^ suffix

let string_of_list prefix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls) ^ suffix

let parens s = "(" ^ s ^ ")"
let comment_parens s = "{- " ^ s ^ " -}"

let is_record_typ inst =
  match inst.it with
  | InstD (_, _, {it = StructT _; _}) -> true
  | _ -> false

let is_variant_typ inst =
  match inst.it with
  | InstD (_, _, {it = VariantT _; _}) -> true
  | _ -> false

let is_alias_typ inst =
  match inst.it with
  | InstD (_, _, {it = AliasT _; _}) -> true
  | _ -> false

let check_trivial_append env typ =
  match typ.it with
  | IterT _ -> true
  | VarT (id, _) ->
    begin match (Il.Env.find_opt_typ env id) with
    | Some (_, [inst]) when is_record_typ inst -> true
    | _ -> false
    end
  | _ -> false

let comment_desc_def d =
  match d.it with
  | TypD (_, _, [inst]) when is_alias_typ inst -> "Type Alias Definition"
  | TypD (_, _, [inst]) when is_variant_typ inst -> "Inductive Type Definition"
  | TypD (_, _, [inst]) when is_record_typ inst -> "Record Creation Definition"
  | TypD _ -> "Type Family Definition"
  | RecD _ -> "Mutual Recursion"
  | DecD (_, _, _, []) -> "Axiom Definition"
  | DecD _ -> "Auxiliary Definition"
  | RelD _ -> "Inductive Relations Definition"
  | HintD _ -> "Hint Definition"
  | GramD _ -> "Grammar Production Definition"

(* bool-valued operators, expression position *)
let render_unop unop =
  match unop with
  | `NotOp   -> "not "
  | `PlusOp  -> ""
  | `MinusOp -> "0 – "
let render_binop binop =
  match binop with
  | `AndOp   -> " ∧ "
  | `OrOp    -> " ∨ "
  | `ImplOp  -> " impliesᵇ "
  | `EquivOp -> " =ᵇ "
  | `AddOp   -> " + "
  | `SubOp   -> " – "
  | `MulOp   -> " * "
  | `DivOp   -> " / "
  | `ModOp   -> " % "
  | `PowOp   -> " ^ "

let render_cmpop cmpop =
  match cmpop with
  | `EqOp -> " =? "
  | `NeOp -> " ≠? "
  | `LtOp -> " <? "
  | `GtOp -> " >? "
  | `LeOp -> " ≤? "
  | `GeOp -> " ≥? "

(* propositional operators, premise position *)
let render_prop_binop binop =
  match binop with
  | `AndOp   -> " × "
  | `OrOp    -> " ⊎ "
  | `ImplOp  -> " → "
  | _ -> " unsupported-prop-binop "

let render_prop_cmpop cmpop =
  match cmpop with
  | `EqOp -> " ≡ "
  | `NeOp -> " ≢ "
  | `LtOp -> " < "
  | `GtOp -> " > "
  | `LeOp -> " ≤ "
  | `GeOp -> " ≥ "

let is_atomid a =
  match a.it with
  | Xl.Atom.Atom _ -> true
  | _ -> false

(* sanitize id: _ mixfix, . reserved -> replace, keyword clash -> prime *)
let render_id id =
  match id with
  | "_" -> "_"
  | _ ->
    let id = String.concat "-" (String.split_on_char '_' id) in
    let id = String.concat "·" (String.split_on_char '.' id) in
    if StringSet.mem id keywords then id ^ "'" else id

let render_atom a =
  match a.it with
  | Xl.Atom.Atom a -> render_id a
  | _ -> ""

let raw_atom a =
  match a.it with
  | Xl.Atom.Atom a -> a
  | _ -> ""

let render_mixop typ_id (m : mixop) =
  let s = String.concat "" (List.map (
    fun atoms -> String.concat "" (List.filter is_atomid atoms |> List.map raw_atom)) (Xl.Mixop.flatten m)
  ) in
  (* HACK - should be done in improve ids *)
  match s with
  | "_" -> "mk-" ^ render_id typ_id
  | s when Il.Env.mem_typ !env_ref.il_env (s $ no_region) -> "mk-" ^ render_id s
  | s -> render_id s

let get_param_id b =
  match b.it with
  | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _, _) -> render_id id.it

let render_numtyp nt =
  match nt with
  | `NatT -> "ℕ"
  | `IntT -> "ℕ" (* TODO proper number types *)
  | `RatT -> "ℕ"
  | `RealT -> "ℕ"

let transform_case_tup e =
  match e.it with
  | TupE exps -> exps
  | _ -> [e]

let transform_case_typ t =
  match t.it with
  | TupT typs -> List.map snd typs
  | _ -> [t]

let transform_case_args t =
  match t.it with
  | TupT typs -> typs
  | _ -> [("_" $ t.at, t)]

let rec has_typ id t =
  match t.it with
  | VarT (id', _) -> id'.it = id
  | IterT (t', _) -> has_typ id t'
  | TupT pairs -> List.exists (fun (_, t') -> has_typ id t') pairs
  | _ -> false

let typ_mentions_var v t =
  Il.Free.Set.mem v (Il.Free.free_typ t).Il.Free.varid

let elem_typ t =
  match t.it with
  | IterT (t', _) -> t'
  | _ -> t

(* types needing Inhabited (lookups/unwraps) or HasEq (comparisons), close over reachable *)
let rec mark_needed selector t =
  match t.it with
  | BoolT | NumT _ | TextT -> ()
  | TupT pairs -> List.iter (fun (_, t') -> mark_needed selector t') pairs
  | IterT (t', _) -> mark_needed selector t'
  | VarT (id, args) ->
    (* type args need instances too *)
    List.iter (fun a -> match a.it with
      | TypA t' -> mark_needed selector t'
      | _ -> ()) args;
    let seen = (match selector with
      | `Inh -> StringSet.mem id.it !env_ref.needed_inh
      | `Eq -> StringSet.mem id.it !env_ref.needed_eq) in
    if not seen then begin
      (match selector with
       | `Inh -> !env_ref.needed_inh <- StringSet.add id.it !env_ref.needed_inh
       | `Eq -> !env_ref.needed_eq <- StringSet.add id.it !env_ref.needed_eq);
      match Il.Env.find_opt_typ !env_ref.il_env id with
      | None -> ()
      | Some (_, insts) ->
        List.iter (fun inst -> match inst.it with
          | InstD (_, _, {it = AliasT t'; _}) -> mark_needed selector t'
          | InstD (_, _, {it = StructT fields; _}) ->
            List.iter (fun (_, (t', _, _), _) -> mark_needed selector t') fields
          | InstD (_, _, {it = VariantT cases; _}) ->
            (match selector with
             | `Eq ->
               List.iter (fun (_, (t', _, _), _) ->
                 List.iter (mark_needed selector) (transform_case_typ t')) cases
             | `Inh ->
               (match List.find_opt (fun (_, (t', _, _), _) ->
                  not (List.exists (has_typ id.it) (transform_case_typ t'))) cases with
                | Some (_, (t', _, _), _) ->
                  List.iter (mark_needed selector) (transform_case_typ t')
                | None -> ()))
        ) insts
    end

let rec render_param_type exp_type param =
  match param.it with
  | ExpP (_, typ) -> render_type exp_type typ
  | TypP _ -> "Set"
  | DefP (_, params, typ) ->
    (* deps: keep binders *)
    string_of_list_suffix " → " " → " (render_param exp_type) params ^ render_type exp_type typ
  | GramP _ -> comment_parens ("Unsupported param: " ^ Il.Print.string_of_param param)

and render_type exp_type typ =
  let rt_func = render_type exp_type in
  match typ.it with
  | VarT (id, []) -> render_id id.it
  | VarT (id, args) ->
    (* family app at determinable args -> matching instance's aux (variant/record) or body (alias), aux names are print-only *)
    let family_inst_render () =
      match Il.Env.find_opt_typ !env_ref.il_env id with
      | Some (_, insts) when List.length insts > 1 ||
          List.exists (fun i -> match i.it with InstD (_, a, _) -> a <> []) insts ->
        let args' = List.map (fun a -> try Il.Eval.reduce_arg !env_ref.il_env a with _ -> a) args in
        let rec find i = function
          | [] -> None
          | inst :: rest ->
            (match inst.it with
             | InstD (quants, iargs, deftyp) ->
               (match (try Il.Eval.match_list Il.Eval.match_arg !env_ref.il_env
                         Il.Subst.empty args' iargs
                       with _ -> None) with
                | Some sub -> Some (i, quants, deftyp, sub)
                | None -> find (i + 1) rest))
        in
        (match find 0 insts with
         | Some (i, quants, deftyp, sub) ->
           (match deftyp.it with
            | AliasT t -> Some (rt_func (Il.Subst.subst_typ sub t))
            | VariantT _ | StructT _ ->
              let aux = render_id id.it ^ "-fam" ^ string_of_int i in
              let qargs = List.map (fun q -> match q.it with
                | ExpP (x, _) ->
                  (match Il.Subst.Map.find_opt x.it sub.Il.Subst.varid with
                   | Some e -> parens (render_exp exp_type e)
                   | None -> "_")
                | TypP x ->
                  (match Il.Subst.Map.find_opt x.it sub.Il.Subst.typid with
                   | Some t -> parens (rt_func t)
                   | None -> "_")
                | _ -> "_") quants in
              Some (if qargs = [] then aux
                    else parens (aux ^ " " ^ String.concat " " qargs)))
         | None -> None)
      | _ -> None
    in
    (match family_inst_render () with
     | Some r -> r
     | None ->
    (* stuck apps (injection args): reduce so overloaded ctors elaborate, but only if fully concrete else defeq breaks *)
    let rec concrete_exp e = (match e.it with
      | VarE _ | CallE _ | TheE _ | IdxE _ -> false
      | CaseE (_, e1) | ProjE (e1, _) | LiftE e1 -> concrete_exp e1
      | TupE es | ListE es -> List.for_all concrete_exp es
      | NumE _ | BoolE _ | TextE _ | OptE None -> true
      | OptE (Some e1) -> concrete_exp e1
      | _ -> false) in
    let rec concrete_typ t = (match t.it with
      | VarT (_, args') -> List.for_all (fun a -> match a.it with
          | ExpA e -> concrete_exp e
          | TypA t' -> concrete_typ t'
          | _ -> true) args'
      | IterT (t', _) -> concrete_typ t'
      | TupT ps -> List.for_all (fun (_, t') -> concrete_typ t') ps
      | _ -> true) in
    let typ' = reduce_typ_safe !env_ref.il_env typ in
    if not (Il.Eq.eq_typ typ' typ) && concrete_typ typ' then rt_func typ'
    else parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type) args)))
  | BoolT -> "Bool"
  | NumT nt -> render_numtyp nt
  | TextT -> "String"
  | TupT [] -> "⊤"
  | TupT typs -> parens (String.concat " × " (List.map (fun (_, t) -> rt_func t) typs))
  | IterT (t, Opt) -> parens ("Maybe " ^ rt_func t)
  | IterT (t, _) -> parens ("List " ^ rt_func t)

and render_exp exp_type exp =
  let r_func = render_exp exp_type in
  match exp.it with
  | VarE id -> render_id id.it
  | BoolE b -> string_of_bool b
  | NumE (`Nat n) when exp_type = LHS ->
    (* agda rejects big pattern literals, suc-expand *)
    let rec expand_unary n =
      if Z.equal n Z.zero then "zero"
      else "suc " ^ parens (expand_unary (Z.pred n)) in
    parens (expand_unary n)
  | NumE (`Nat n) -> Z.to_string n
  | NumE (`Int n) -> Z.to_string n (* TODO fix nums *)
  | NumE (`Rat n) -> Q.to_string n (* TODO fix nums *)
  | NumE (`Real n) -> string_of_float n (* TODO fix nums *)
  | TextE s -> "\"" ^ String.escaped s ^ "\""
  | UnE (unop, _, e1) -> parens (render_unop unop ^ r_func e1)
  | BinE (binop, _, e1, e2) -> parens (r_func e1 ^ render_binop binop ^ r_func e2)
  | CmpE (cmpop, _, e1, e2) -> parens (r_func e1 ^ render_cmpop cmpop ^ r_func e2)
  | TupE [] -> "tt"
  | TupE exps -> parens (String.concat " , " (List.map r_func exps))
  | ProjE (e, i) ->
    let typs = transform_case_typ e.note in
    (* tuples right-nested: a × (b × c) *)
    let rec proj2s k s = if k = 0 then s else parens ("proj₂ " ^ proj2s (k - 1) s) in
    let len = List.length typs - 1 in
    begin match typs with
    | [_] -> r_func e
    | _ -> if i = len then proj2s len (r_func e) else parens ("proj₁ " ^ proj2s i (r_func e))
    end
  | CaseE (m, e) ->
    let name = Il.Print.string_of_typ_name (reduce_typ_safe !env_ref.il_env exp.note) in
    let exps = transform_case_tup e in
    (* data params implicit in ctors, no placeholders unlike Rocq *)
    begin match exps with
    | [] -> render_mixop name m
    | _ -> parens (render_mixop name m ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | UncaseE _ -> error exp.at "Encountered uncase. Run uncase-removal pass"
  | OptE (Some e) -> parens ("just " ^ r_func e)
  | OptE None -> "nothing"
  | TheE e -> parens ("unwrap! " ^ r_func e)
  | StrE fields -> "record { " ^ (String.concat " ; " (List.map (fun (a, e) ->
    render_atom a ^ " = " ^ r_func e) fields)) ^ " }"
  | DotE (e, a) -> parens (render_atom a ^ " " ^ r_func e)
  | CompE (e1, e2) -> parens (r_func e1 ^ " ⧺ " ^ r_func e2)
  | ListE [] -> "[]"
  | ListE exps ->
    (* ctor elems overloaded across instances, ascribe elem type *)
    let has_case = List.exists (fun e' -> match e'.it with CaseE _ -> true | _ -> false) exps in
    let lit = String.concat " ∷ " (List.map r_func exps) ^ " ∷ []" in
    if has_case then parens ("as " ^ render_type exp_type exp.note ^ " " ^ parens lit)
    else parens lit
  | LiftE e -> parens ("fromMaybe " ^ r_func e)
  | MemE (e1, e2) -> parens (r_func e1 ^ " ∈ᵇ " ^ r_func e2)
  | LenE e1 -> parens ("length " ^ r_func e1)
  | CatE ({it = ListE [e1]; _}, e2) when exp_type = LHS -> parens (r_func e1 ^ " ∷ " ^ r_func e2)
  | CatE (e1, e2) -> parens (r_func e1 ^ " ++ " ^ r_func e2)
  | IdxE (e1, e2) -> parens (r_func e1 ^ " [ " ^ r_func e2 ^ " ]!")
  | SliceE (e1, e2, e3) -> parens ("slice " ^ r_func e1 ^ " " ^ r_func e2 ^ " " ^ r_func e3)
  | UpdE (e1, p, e2) -> render_path_start p e1 false e2
  | ExtE (e1, p, e2) -> render_path_start p e1 true e2
  | CallE (id, [a]) when StringSet.mem id.it !env_ref.proj_set ->
    parens ("coerce {B = " ^ render_type exp_type exp.note ^ "} " ^ parens (render_arg exp_type a))
  | CallE (id, args) -> parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type) args))
  (* Iter handling *)
  | IterE (e, (ListN (n, Some id), [])) ->
    parens ("mkseq " ^ render_lambda [render_id id.it] (r_func e) ^ " " ^ (r_func n))
  | IterE (e, (ListN (n, None), [])) ->
    (* list body: dim is annotation, else replicated constant *)
    if Il.Eq.eq_typ e.note exp.note then r_func e
    else parens ("replicate " ^ (r_func n) ^ " " ^ (r_func e))
  | IterE (e, (Opt, [])) ->
    (* constant option: lift unless already optional *)
    if Il.Eq.eq_typ e.note exp.note then r_func e
    else parens ("just " ^ r_func e)
  | IterE (e, (List, [])) ->
    (* constant list: singleton unless already a list *)
    if Il.Eq.eq_typ e.note exp.note then r_func e
    else parens (r_func e ^ " ∷ []")
  | IterE (e, (_, [])) -> r_func e
  (* identity iter kept for dimension, render source *)
  | IterE ({it = VarE x; _}, (ListN _, [(x', src)])) when x.it = x'.it ->
    render_exp exp_type src
  | IterE (e, _) when exp_type = LHS -> r_func e
  | IterE (e, (iter, iter_quants)) ->
    let quants = List.map (fun (id, e) -> parens (render_id id.it ^ " : " ^ render_type exp_type (remove_iter_from_type e.note))) iter_quants in
    let iter_exps = List.map snd iter_quants in
    let n = List.length iter_quants - 1 in
    let lst = if iter = Opt then iter_exp_opt_funcs else iter_exp_lst_funcs in
    let pred_name = match (List.nth_opt lst n) with
    | Some s -> s
    | None -> error exp.at "Iteration exceeded the supported amount for Agda translation"
    in
    parens (pred_name ^ " " ^ render_lambda quants (r_func e) ^ " " ^
    String.concat " " (List.map (render_exp exp_type) iter_exps))
  | CvtE (e1, _nt1, nt2) -> parens ("coerce {B = " ^ render_numtyp nt2 ^ "} " ^ r_func e1)
  | SubE _ -> error exp.at "Encountered subtype expression. Please run sub pass"
  | IfE (e1, e2, e3) -> parens ("if " ^ r_func e1 ^ " then " ^ r_func e2 ^ " else " ^ r_func e3)

and render_arg exp_type a =
  match a.it with
  | ExpA e -> render_exp exp_type e
  | TypA t -> render_type exp_type t
  | DefA id -> render_id id.it
  | _ -> comment_parens ("Unsupported arg: " ^ Il.Print.string_of_arg a)

and render_quant exp_type b =
  match b.it with
  | ExpP (id, typ) -> parens (render_id id.it ^ " : " ^ render_type exp_type typ)
  | TypP id -> parens (render_id id.it ^ " : Set")
  | DefP (id, params, typ) ->
    parens (render_id id.it ^ " : " ^
    string_of_list_suffix " → " " → " (render_param exp_type) params ^
    render_type exp_type typ)
  | GramP _ -> comment_parens ("Unsupported quant: " ^ Il.Print.string_of_quant b)

and render_param exp_type param =
  parens (get_param_id param ^ " : " ^ render_param_type exp_type param)

(* PATH Functions *)
and transform_list_path (p : path) =
  match p.it with
  | RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) when p'.it = RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) -> p' :: transform_list_path p'

and render_lambda quants text =
  parens ("λ " ^ String.concat " " quants ^ " → " ^ text)

and render_path_start (p : path) start_exp is_extend end_exp =
  let paths = List.rev (p :: transform_list_path p) in
  (render_path paths (start_exp.note) p.at 0 (Some start_exp) is_extend end_exp)

and render_path (paths : path list) typ at n name is_extend end_exp =
  let render_record_update t1 t2 t3 =
    parens ("record " ^ t1 ^ " { " ^ t2 ^ " = " ^ t3 ^ " }")
  in
  let r_func_e = render_exp RHS in
  let list_name num = (match name with
    | Some exp -> exp
    | None -> VarE ((var_prefix ^ string_of_int num) $ no_region) $$ no_region % typ
  ) in
  let new_name_typ = remove_iter_from_type (list_name n).note in
  let new_name = var_prefix ^ string_of_int (n + 1) in
  match paths with
  (* End logic for extend *)
  | [{it = IdxP (_, e); _}] when is_extend ->
    let extend_term = parens (new_name ^ " ⧺ " ^ r_func_e end_exp) in
    let quant = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [quant] extend_term)
  | [{it = DotP (_p, a); _}] when is_extend ->
    let projection_term = parens (render_atom a ^ " " ^ r_func_e (list_name n)) in
    let extend_term = parens (projection_term ^ " ⧺ " ^ r_func_e end_exp) in
    render_record_update (r_func_e (list_name n)) (render_atom a) extend_term
  | [{it = SliceP (_, _e1, _e2); _} as p] when is_extend ->
    (* TODO - extending a slice *)
    comment_parens (Il.Print.string_of_path p)
  (* End logic for update *)
  | [{it = IdxP (_, e); _}] ->
    let quant = render_quant RHS (ExpP ("_" $ no_region, new_name_typ) $ no_region) in
    parens ("modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [quant] (r_func_e end_exp))
  | [{it = DotP (_p, a); _}] ->
    render_record_update (r_func_e (list_name n)) (render_atom a) (r_func_e end_exp)
  | [{it = SliceP (_, e1, e2); _}] ->
    parens ("slice-update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ r_func_e end_exp)
  (* Middle logic *)
  | {it = IdxP (_, e); note; _} :: ps ->
    let path_term = render_path ps note at (n + 1) None is_extend end_exp in
    let quant = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [quant] path_term)
  | {it = DotP (_p, a); note; _} :: ps ->
    (* nested record updates *)
    let inner_exp = DotE (list_name n, a) $$ no_region % note in
    let path_term = render_path ps note at n (Some inner_exp) is_extend end_exp in
    render_record_update (r_func_e (list_name n)) (render_atom a) path_term
  | ({it = SliceP (_, _e1, _e2); _} as p) :: _ps ->
    (* TODO - still unsure how to implement this as a term *)
    comment_parens (Il.Print.string_of_path p)
  (* Catch all error if we encounter empty list or RootP *)
  | _ -> error at "Paths should not be empty"

and render_quants (quants : quant list) =
  string_of_list_prefix " " " " (render_quant RHS) quants

let render_quants_ids (quants : quant list) =
  string_of_list_prefix " " " " get_param_id quants

let render_params params =
  string_of_list_prefix " " " " (render_param RHS) params

let render_match_args args =
  string_of_list_prefix " " " " (render_arg LHS) args

let string_of_relation_args typ =
  string_of_list "" " → " " → " (render_type RHS) (transform_case_typ typ)

(* premises propositional: cmp/connectives -> Set ops, bool exps lifted with is-true *)
let is_prop_shaped e =
  match e.it with
  | CmpE _ | BinE _ | UnE (`NotOp, _, _) | MemE _ -> true
  | _ -> false

let rec render_prop_exp e =
  match e.it with
  | CmpE (cmpop, _, e1, e2) ->
    parens (render_exp RHS e1 ^ render_prop_cmpop cmpop ^ render_exp RHS e2)
  | BinE (`EquivOp, _, e1, e2) ->
    parens (parens (render_prop_operand e1 ^ " → " ^ render_prop_operand e2) ^ " × " ^
            parens (render_prop_operand e2 ^ " → " ^ render_prop_operand e1))
  | BinE ((`AndOp | `OrOp | `ImplOp) as binop, _, e1, e2) ->
    parens (render_prop_operand e1 ^ render_prop_binop binop ^ render_prop_operand e2)
  | UnE (`NotOp, _, e1) -> parens ("¬ " ^ render_prop_operand e1)
  | MemE (e1, e2) -> parens (render_exp RHS e1 ^ " ∈ " ^ render_exp RHS e2)
  | _ -> render_prop_operand e

and render_prop_operand e =
  if is_prop_shaped e then render_prop_exp e
  else parens ("is-true " ^ render_exp RHS e)

(* all-ctor clauses may be partial, add default-val catch-all *)
let is_var_pattern a =
  let rec var_exp e = match e.it with
    | VarE _ -> true
    | TupE es -> List.for_all var_exp es
    | IterE (e', (_, _)) -> var_exp e'
    | _ -> false in
  match a.it with
  | ExpA e -> var_exp e
  | TypA _ | DefA _ | GramA _ -> true

let needs_catch_all clauses =
  List.length clauses > 0 &&
  not (List.exists (fun cl -> match cl.it with
    | DefD (_, args, _, _) -> List.for_all is_var_pattern args) clauses)

(* collect Inhabited/HasEq needs, only bool-position cmp marks HasEq *)
let collect_needed_script il =
  let base : unit Il.Walk.collector = Il.Walk.base_collector () (fun () () -> ()) in
  let c = { base with Il.Walk.collect_exp = (fun e ->
      (match e.it with
       | IdxE (e1, _) -> mark_needed `Inh (elem_typ e1.note)
       | TheE _ -> mark_needed `Inh e.note
       | CmpE ((`EqOp | `NeOp), _, e1, _) -> mark_needed `Eq e1.note
       | MemE (e1, _) -> mark_needed `Eq e1.note
       | _ -> ());
      ((), true)) } in
  let go_value e = ignore (Il.Walk.collect_exp c e) in
  let go_arg a = ignore (Il.Walk.collect_arg c a) in
  let rec go_prop_exp e =
    match e.it with
    | CmpE (_, _, e1, e2) -> go_value e1; go_value e2
    | BinE ((`AndOp | `OrOp | `ImplOp | `EquivOp), _, e1, e2) ->
      go_prop_operand e1; go_prop_operand e2
    | UnE (`NotOp, _, e1) -> go_prop_operand e1
    | MemE (e1, e2) -> go_value e1; go_value e2
    | _ -> go_value e
  and go_prop_operand e =
    if is_prop_shaped e then go_prop_exp e else go_value e
  in
  let rec go_prem p = match p.it with
    | IfPr e -> go_prop_exp e
    | RulePr (_, args, _, e) -> List.iter go_arg args; go_value e
    | LetPr (_, e1, e2) -> go_value e1; go_value e2
    | ElsePr -> ()
    | IterPr (p', (_, ides)) -> go_prem p'; List.iter (fun (_, e) -> go_value e) ides
    | NegPr p' -> go_prem p'
  in
  let rec go_def d = match d.it with
    | RecD ds -> List.iter go_def ds
    | DecD (_, _, typ, clauses) ->
      if needs_catch_all clauses then mark_needed `Inh typ;
      List.iter (fun cl -> match cl.it with
        | DefD (_, args, e, prems) ->
          List.iter go_arg args; go_value e; List.iter go_prem prems) clauses
    | RelD (_, _, _, _, rules) ->
      List.iter (fun r -> match r.it with
        | RuleD (_, _, _, e, prems) -> go_value e; List.iter go_prem prems) rules
    | TypD (_, _, insts) ->
      List.iter (fun inst -> match inst.it with
        | InstD (_, _, {it = VariantT cases; _}) ->
          List.iter (fun (_, (_, _, prems), _) -> List.iter go_prem prems) cases
        | _ -> ()) insts
    | _ -> ()
  in
  List.iter go_def il

let rec render_prem prem =
  let r_func = render_prem in
  match prem.it with
  | IfPr exp -> render_prop_exp exp
  | RulePr (id, args, _m, exp) -> parens (render_id id.it ^ string_of_list_prefix " " " " (render_arg RHS) args ^
    string_of_list_prefix " " " " (render_exp RHS) (transform_case_tup exp))
  | NegPr p -> parens ("¬ " ^ r_func p)
  | ElsePr -> "⊤ " ^ comment_parens ("Unsupported premise: otherwise") (* Will be removed by an else pass *)
  | IterPr (p, (ListN (e, Some i), [])) ->
    "holds-upto " ^ render_lambda [render_id i.it] (r_func p) ^ " " ^ (render_exp RHS e)
  | IterPr (p, (_, [])) -> r_func p
  | IterPr (p, (ListN (_, Some i), ps)) ->
    let quants = List.map (fun (id, e) -> parens (render_id id.it ^ " : " ^ render_type RHS (remove_iter_from_type e.note))) ps in
    let iter_exps = List.map snd ps in
    let n = List.length ps - 1 in
    let pred_name = match (List.nth_opt sup_iter_prem_rels_list n) with
    | Some s -> s
    | None -> error prem.at "Iteration exceeded the supported amount for Agda translation"
    in
    pred_name ^ " " ^ render_lambda (render_id i.it :: quants) (r_func p) ^ " " ^
    String.concat " " (List.map (render_exp RHS) iter_exps)
  | IterPr (p, (iter, ps)) ->
    let option_conversion s = if iter = Opt then parens ("fromMaybe " ^ s) else s in
    let quants = List.map (fun (id, e) -> parens (render_id id.it ^ " : " ^ render_type RHS (remove_iter_from_type e.note))) ps in
    let iter_exps = List.map snd ps in
    let n = List.length ps - 1 in
    let pred_name = match (List.nth_opt iter_prem_rels_list n) with
    | Some s -> s
    | None -> error prem.at "Iteration exceeded the supported amount for Agda translation"
    in
    pred_name ^ " " ^ render_lambda quants (r_func p) ^ " " ^
    String.concat " " (List.map (render_exp RHS) iter_exps |> List.map option_conversion)
  | LetPr (_, e1, e2) ->
    "let " ^ render_exp LHS e1 ^ " = " ^ render_exp RHS e2 ^ " in "

(* agda lets need record patterns, ctor-pattern let -> pattern-lambda app *)
let rec is_irrefutable e =
  match e.it with
  | VarE _ -> true
  | TupE es -> List.for_all is_irrefutable es
  | IterE (e1, _) -> is_irrefutable e1
  | _ -> false

let wrap_let_prems ?(codomain = "Set") let_prems inner =
  List.fold_right (fun pr acc -> match pr.it with
    | LetPr (_, e1, e2) ->
      if is_irrefutable e1 then
        "let " ^ render_exp LHS e1 ^ " = " ^ render_exp RHS e2 ^ " in " ^ acc
      else
        (* pattern lambdas not inferable, ascribe head *)
        parens ("(as " ^ parens (render_type RHS e2.note ^ " → " ^ codomain) ^
                " (λ { " ^ parens (render_exp LHS e1) ^ " → " ^ acc ^ " })) " ^
                parens (render_exp RHS e2))
    | _ -> acc) let_prems inner

let render_typealias id quants typ =
  id ^ " : " ^ string_of_list_suffix " → " " → " (render_quant RHS) quants ^ "Set\n" ^
  id ^ render_quants_ids quants ^ " = " ^ render_type RHS typ

let render_record id quants fields =
  let constructor_name = "mk-" ^ id in
  let record_quanters = render_quants quants in
  let quanter_ids = render_quants_ids quants in

  (* record def, open brings field projections into scope *)
  "record " ^ id ^ record_quanters ^ " : Set where\n" ^
  "  constructor " ^ constructor_name ^ "\n" ^
  "  field\n" ^
  String.concat "\n" (List.map (fun (a, (typ, _, _), _) ->
    "    " ^ render_atom a ^ " : " ^ render_type RHS typ) fields) ^ "\n" ^
  "open " ^ id ^ "\n\n" ^

  (* Append instance *)
  "instance\n" ^
  "  append-" ^ id ^ " : " ^ string_of_list_suffix " → " " → " (render_quant RHS) quants ^ "HasAppend " ^ parens (id ^ quanter_ids) ^ "\n" ^
  "  append-" ^ id ^ record_quanters ^ " = record { append = λ arg1 arg2 → record {\n    " ^
  String.concat " ;\n    " ((List.map (fun (a, (t, _, _), _) ->
    let record_id' = render_atom a in
    if (check_trivial_append !env_ref.il_env t)
    then record_id' ^ " = " ^ record_id' ^ " arg1 ⧺ " ^ record_id' ^ " arg2"
    else record_id' ^ " = " ^ record_id' ^ " arg1 " ^ comment_parens "FIXME - Non-trivial append"
  )) fields) ^ " } }"

let render_coercion (base_typ, typ_params) coerc_typ proj_func_id =
  let implicit_params = string_of_list_suffix " → " " → "
    (fun p -> "{" ^ get_param_id p ^ " : " ^ render_param_type RHS p ^ "}") typ_params in
  let underscores = String.concat "" (List.map (fun _ -> " _") typ_params) in
  "instance\n" ^
  "  " ^ proj_func_id ^ "-coercion : " ^ implicit_params ^ "Coerce " ^ base_typ ^ " " ^ coerc_typ ^ "\n" ^
  "  " ^ proj_func_id ^ "-coercion = record { coerce = " ^ proj_func_id ^ underscores ^ " }"

let render_case_typs t =
  let typs = transform_case_args t in
  string_of_list_suffix " → " " → " (fun (i, t) ->
    parens (render_id i.it ^ " : " ^ render_type RHS t)) typs

(* eq premise p = e fixes type param p for the case *)
let case_eq_prem_on p prems =
  List.find_map (fun prem -> match prem.it with
    | IfPr {it = CmpE (`EqOp, _, {it = VarE x; _}, e); _} when x.it = p -> Some e
    | IfPr {it = CmpE (`EqOp, _, e, {it = VarE x; _}); _} when x.it = p -> Some e
    | _ -> None) prems

let is_eq_prem_on ids prem =
  List.exists (fun p -> case_eq_prem_on p [prem] <> None) ids

let quant_raw_id q =
  match q.it with
  | ExpP (i, _) | TypP i | DefP (i, _, _) | GramP (i, _, _) -> i.it

let variant_indexed quants cases =
  List.filter (fun q ->
    List.exists (fun (_, (_, _, prems), _) -> case_eq_prem_on (quant_raw_id q) prems <> None) cases
  ) quants

let render_variant_typ id quants cases =
  (* eq-constrained type params become GADT indices via result type, unconstrained -> implicit, other premises dropped *)
  let param_id = quant_raw_id in
  let indexed = variant_indexed quants cases in
  let indexed_ids = List.map param_id indexed in
  let params = List.filter (fun q -> not (List.mem (param_id q) indexed_ids)) quants in
  let index_typs = string_of_list_suffix " → " " → " (render_param_type RHS) indexed in
  let render_case (m, (t, _quants', prems), _) =
    let implicit_binders = List.filter_map (fun q ->
      match case_eq_prem_on (param_id q) prems with
      | Some _ -> None
      | None -> Some ("{" ^ render_id (param_id q) ^ " : " ^ render_param_type RHS q ^ "} → ")
    ) indexed |> String.concat "" in
    let result_indices = string_of_list_prefix " " " " (fun q ->
      match case_eq_prem_on (param_id q) prems with
      | Some e -> parens (render_exp RHS e)
      | None -> render_id (param_id q)
    ) indexed in
    let dropped = List.filter (fun p -> not (is_eq_prem_on indexed_ids p)) prems in
    let dropped_comment =
      if dropped = [] then ""
      else " " ^ comment_parens (string_of_int (List.length dropped) ^ " premise(s) dropped") in
    render_mixop id m ^ " : " ^ implicit_binders ^ render_case_typs t ^
    id ^ render_quants_ids params ^ result_indices ^ dropped_comment
  in
  "data " ^ id ^ render_quants params ^ " : " ^ index_typs ^ "Set where\n  " ^
  String.concat "\n  " (List.map render_case cases)

let is_family_typ id =
  match Il.Env.find_opt_typ !env_ref.il_env id with
  | Some (_, insts) ->
    List.length insts > 1 ||
    List.exists (fun i -> match i.it with InstD (_, args, _) -> args <> []) insts
  | None -> false

(* default value as term, family apps call generated helper *)
let rec render_default_term t =
  match t.it with
  | IterT (_, Opt) -> "nothing"
  | IterT (_, _) -> "[]"
  | TupT [] -> "tt"
  | TupT ts -> parens (String.concat " , " (List.map (fun (_, t') -> render_default_term t') ts))
  | VarT (id, args) when is_family_typ id ->
    parens ("Inhabited.default-val " ^
      parens ("inh-" ^ render_id id.it ^ "-fun" ^
        string_of_list_prefix " " " " (render_arg RHS) args))
  | _ -> "default-val"

(* poly fn may use eq/default at param, thread class constraints *)
let clauses_need pred clauses =
  let c = { Il.Walk.exists_base_checker with Il.Walk.collect_exp = (fun e -> (pred e, true)) } in
  List.exists (fun clause -> match clause.it with
    | DefD (_, args, e, prems) ->
      List.exists (fun a -> Il.Walk.collect_arg c a) args ||
      Il.Walk.collect_exp c e ||
      List.exists (fun p -> Il.Walk.collect_prem c p) prems) clauses

(* generated Inhabited + HasEq instances, after type defs *)
(* does default at t need default for param p, not under list/option *)
let rec typ_needs_inh_param p t =
  match t.it with
  | VarT (id, []) -> id.it = p
  | VarT (_, _) -> has_typ p t
  | TupT pairs -> List.exists (fun (_, t') -> typ_needs_inh_param p t') pairs
  | IterT _ -> false
  | _ -> false

let instance_binders ?(needs = fun _ -> true) cls quants =
  String.concat "" (List.map (fun q ->
    match q.it with
    | TypP i ->
      "{" ^ render_id i.it ^ " : Set} → " ^
      (if needs i.it then "{{" ^ cls ^ " " ^ render_id i.it ^ "}} → " else "")
    | ExpP (i, t) -> "{" ^ render_id i.it ^ " : " ^ render_type RHS t ^ "} → "
    | _ -> "") quants)

let instance_target id quants =
  if quants = [] then id else parens (id ^ render_quants_ids quants)

let render_inhabited_record raw_id id quants fields =
  if not (StringSet.mem raw_id !env_ref.needed_inh) then "" else
  let needs p = List.exists (fun (_, (t, _, _), _) -> typ_needs_inh_param p t) fields in
  "\n\ninstance\n" ^
  "  inh-" ^ id ^ " : " ^ instance_binders ~needs "Inhabited" quants ^ "Inhabited " ^ instance_target id quants ^ "\n" ^
  "  inh-" ^ id ^ String.concat "" (List.map (fun q -> " {" ^ get_param_id q ^ "}") quants) ^ " = record { default-val = record { " ^
  String.concat " ; " (List.map (fun (a, _, _) -> render_atom a ^ " = default-val") fields) ^
  " } }"

let render_inhabited_variant raw_id id quants cases =
  if not (StringSet.mem raw_id !env_ref.needed_inh) then "" else
  if variant_indexed quants cases <> [] then "" else
  match List.find_opt (fun (_, (t, _, _), _) ->
    not (List.exists (has_typ raw_id) (transform_case_typ t))) cases with
  | None -> ""
  | Some (m, (t, _, _), _) ->
    let raw_comps = transform_case_args t in
    (* let-bind component only if a later component's type depends on it *)
    let comps = List.mapi (fun i (x, ti) ->
      let referenced = List.exists (fun (_, tj) -> typ_mentions_var x.it tj)
        (Util.Lib.List.drop (i + 1) raw_comps) in
      (x, ti, referenced)) raw_comps in
    let lets = String.concat "" (List.filter_map (fun (x, ti, r) ->
      if r then Some ("let " ^ render_id x.it ^ " = " ^ render_default_term ti ^ " in ")
      else None) comps) in
    let ctor = render_mixop id m in
    let args_str = String.concat "" (List.map (fun (x, ti, r) ->
      if r then " " ^ render_id x.it else " " ^ parens (render_default_term ti)) comps) in
    let value =
      if comps = [] then ctor
      else parens (lets ^ ctor ^ args_str) in
    let needs p = List.exists (typ_needs_inh_param p) (transform_case_typ t) in
    "\n\ninstance\n" ^
    "  inh-" ^ id ^ " : " ^ instance_binders ~needs "Inhabited" quants ^ "Inhabited " ^ instance_target id quants ^ "\n" ^
    "  inh-" ^ id ^ String.concat "" (List.map (fun q -> " {" ^ get_param_id q ^ "}") quants) ^ " = record { default-val = " ^ value ^ " }"

(* cmp term for component type, group-recursive calls siblings via helpers for structural recursion, returns term, helpers, deep-recursion flag *)
let eq_cmp_term group t x y =
  let helpers = ref [] in
  let deep = ref false in
  let rec mentions t = match t.it with
    | VarT (id, args) ->
      StringSet.mem id.it group ||
      List.exists (fun a -> match a.it with
        | TypA t' -> mentions t'
        | _ -> false) args
    | IterT (t', _) -> mentions t'
    | TupT ps -> List.exists (fun (_, t') -> mentions t') ps
    | _ -> false in
  let shape_key t =
    String.map (fun c ->
      if (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') then c else '-')
      (render_type RHS t) in
  (* name of Bool cmp fn for t, emits helpers as needed *)
  let rec cmp_fun t =
    match t.it with
    | VarT (tid, []) when StringSet.mem tid.it group ->
      Some ("eq-" ^ render_id tid.it ^ "-fun")
    | IterT (t', (List | List1)) when mentions t' ->
      (match cmp_fun t' with
       | None -> None
       | Some ef ->
         let hid = "eq-" ^ shape_key t' ^ "-lst-fun" in
         emit_helper hid (fun () ->
           let elem = render_type RHS t' in
           hid ^ " : List " ^ elem ^ " → List " ^ elem ^ " → Bool\n" ^
           hid ^ " [] [] = true\n" ^
           hid ^ " (x ∷ xs) (y ∷ ys) = (" ^ ef ^ " x y) ∧ (" ^ hid ^ " xs ys)\n" ^
           hid ^ " _ _ = false");
         Some hid)
    | IterT (t', Opt) when mentions t' ->
      (match cmp_fun t' with
       | None -> None
       | Some ef ->
         let hid = "eq-" ^ shape_key t' ^ "-opt-fun" in
         emit_helper hid (fun () ->
           let elem = render_type RHS t' in
           hid ^ " : Maybe " ^ elem ^ " → Maybe " ^ elem ^ " → Bool\n" ^
           hid ^ " nothing nothing = true\n" ^
           hid ^ " (just x) (just y) = " ^ ef ^ " x y\n" ^
           hid ^ " _ _ = false");
         Some hid)
    | VarT (fam, _) when mentions t && is_family_typ fam ->
      (* single-inst single-case wrapper family, unwrap and compare payload *)
      (match Il.Env.find_opt_typ !env_ref.il_env fam with
       | Some (_, [{it = InstD (_, _, {it = VariantT [ (m, (ct, _, _), _) ]; _}); _}]) ->
         let comps = transform_case_typ ct in
         (match comps with
          | [payload] ->
            (* instantiate payload with family args *)
            let payload' =
              (match Il.Env.find_opt_typ !env_ref.il_env fam with
               | Some ([{it = TypP x; _}], _) ->
                 (match t.it with
                  | VarT (_, [{it = TypA targ; _}]) ->
                    Il.Subst.subst_typ (Il.Subst.add_typid Il.Subst.empty x targ) payload
                  | _ -> payload)
               | _ -> payload) in
            (match cmp_fun payload' with
             | None -> None
             | Some ef ->
               let ctor = render_mixop (render_id fam.it) m in
               let hid = "eq-" ^ shape_key t ^ "-fam-fun" in
               emit_helper hid (fun () ->
                 let whole = render_type RHS t in
                 hid ^ " : " ^ whole ^ " → " ^ whole ^ " → Bool\n" ^
                 hid ^ " (" ^ ctor ^ " x) (" ^ ctor ^ " y) = " ^ ef ^ " x y");
               Some hid)
          | _ -> None)
       | _ -> None)
    | TupT pairs when mentions t ->
      let subs = List.map (fun (_, t') ->
        if mentions t' then cmp_fun t' else Some "_=?_") pairs in
      if List.exists (fun o -> o = None) subs then None
      else begin
        let hid = "eq-" ^ shape_key t ^ "-tup-fun" in
        emit_helper hid (fun () ->
          let whole = render_type RHS t in
          let n = List.length pairs in
          let xs = List.init n (fun i -> "x" ^ string_of_int i) in
          let ys = List.init n (fun i -> "y" ^ string_of_int i) in
          hid ^ " : " ^ whole ^ " → " ^ whole ^ " → Bool\n" ^
          hid ^ " (" ^ String.concat " , " xs ^ ") (" ^ String.concat " , " ys ^ ") = " ^
          String.concat " ∧ " (List.map2 (fun (o, x) y ->
            (match o with Some f when f <> "_=?_" -> parens (f ^ " " ^ x ^ " " ^ y)
             | _ -> parens (x ^ " =? " ^ y))) (List.combine subs xs) ys));
        Some hid
      end
    | _ when mentions t -> None
    | _ -> None
  and emit_helper hid mk =
    if not (StringSet.mem hid !env_ref.eq_helpers) then begin
      !env_ref.eq_helpers <- StringSet.add hid !env_ref.eq_helpers;
      helpers := !helpers @ [mk ()]
    end
  in
  let term =
    if mentions t then
      match cmp_fun t with
      | Some f -> parens (f ^ " " ^ x ^ " " ^ y)
      | None -> deep := true; parens (x ^ " =? " ^ y)
    else parens (x ^ " =? " ^ y)
  in
  (term, !helpers, !deep)

let render_haseq_record raw_id id quants fields =
  if not (StringSet.mem raw_id !env_ref.needed_eq) then "" else
  if StringSet.mem raw_id !env_ref.eq_skip then "" else
  let group = StringSet.add raw_id !env_ref.cur_group in
  let cmps = List.map (fun (a, (t, _, _), _) ->
    eq_cmp_term group t (parens (render_atom a ^ " r1")) (parens (render_atom a ^ " r2"))) fields in
  let helpers = List.concat_map (fun (_, h, _) -> h) cmps in
  let deep = List.exists (fun (_, _, d) -> d) cmps in
  let fun_name = "eq-" ^ id ^ "-fun" in
  let body = (match cmps with
    | [] -> "true"
    | _ -> String.concat " ∧ " (List.map (fun (c, _, _) -> c) cmps)) in
  "\n\n" ^
  String.concat "\n" helpers ^ (if helpers = [] then "" else "\n") ^
  (if deep then "{-# TERMINATING #-}\n" else "") ^
  fun_name ^ " : " ^ instance_binders "HasEq" quants ^ instance_target id quants ^ " → " ^ instance_target id quants ^ " → Bool\n" ^
  fun_name ^ " r1 r2 = " ^ body ^ "\n" ^
  "instance\n" ^
  "  haseq-" ^ id ^ " : " ^ instance_binders "HasEq" quants ^ "HasEq " ^ instance_target id quants ^ "\n" ^
  "  haseq-" ^ id ^ " = record { _=?_ = " ^ fun_name ^ " }"

let case_args_dependent t =
  let rec go bound = function
    | [] -> false
    | (i, ti) :: rest ->
      List.exists (fun b -> typ_mentions_var b ti) bound || go (i.it :: bound) rest
  in
  go [] (transform_case_args t)

let render_haseq_variant raw_id id quants cases =
  if not (StringSet.mem raw_id !env_ref.needed_eq) then "" else
  if StringSet.mem raw_id !env_ref.eq_skip then "" else
  if variant_indexed quants cases <> [] then "" else
  (* bool eq can't compare dependent components positionally *)
  if List.exists (fun (_, (t, _, _), _) -> case_args_dependent t) cases then "" else
  let fun_name = "eq-" ^ id ^ "-fun" in
  let group = StringSet.add raw_id !env_ref.cur_group in
  let all_helpers = ref [] in
  let any_deep = ref false in
  let case_clause (m, (t, _, _), _) =
    let comps = transform_case_typ t in
    let n = List.length comps in
    let xs = List.init n (fun i -> "x" ^ string_of_int i) in
    let ys = List.init n (fun i -> "y" ^ string_of_int i) in
    let ctor = render_mixop id m in
    let pat vars = if vars = [] then ctor else parens (ctor ^ " " ^ String.concat " " vars) in
    let cmps = List.map2 (fun (x, y) ti ->
      let (c, hs, d) = eq_cmp_term group ti x y in
      all_helpers := !all_helpers @ hs;
      if d then any_deep := true;
      c
    ) (List.combine xs ys) comps in
    let body = if n = 0 then "true" else String.concat " ∧ " cmps in
    fun_name ^ " " ^ pat xs ^ " " ^ pat ys ^ " = " ^ body
  in
  let clauses_str = String.concat "\n" (List.map case_clause cases) in
  let catch_all = if List.length cases > 1 then "\n" ^ fun_name ^ " _ _ = false" else "" in
  "\n\n" ^
  String.concat "\n" !all_helpers ^ (if !all_helpers = [] then "" else "\n") ^
  (if !any_deep then "{-# TERMINATING #-}\n" else "") ^
  fun_name ^ " : " ^ instance_binders "HasEq" quants ^ instance_target id quants ^ " → " ^ instance_target id quants ^ " → Bool\n" ^
  clauses_str ^ catch_all ^ "\n" ^
  "instance\n" ^
  "  haseq-" ^ id ^ " : " ^ instance_binders "HasEq" quants ^ "HasEq " ^ instance_target id quants ^ "\n" ^
  "  haseq-" ^ id ^ " = record { _=?_ = " ^ fun_name ^ " }"

let render_single_type id at params =
  (* last param is projected value, preceding become implicit args *)
  match List.rev params with
  | {it = ExpP (_, typ); _} :: ps -> (render_type RHS typ, List.rev ps)
  | _ -> error at ("Given projection function: " ^ id ^ " has invalid parameters!")

let render_wfness_func_lemma id rule =
  let RuleD (_, quants, _, _, prems) = rule.it in
  let forall_quantifiers = string_of_list "∀ " " → " " " (render_param RHS) quants in
  let letprems, others = List.partition is_let prems in
  let string_prems = string_of_list "" "" " → " render_prem others in
  (* single line, postulate opens a layout block *)
  "postulate " ^ id ^ " : " ^ forall_quantifiers ^ wrap_let_prems letprems string_prems

(* dependent/GADT ctors admit no generated bool eq, nor containers, fixpoint *)
let compute_eq_ineligible il =
  let typs = ref [] in
  let rec collect d = match d.it with
    | RecD ds -> List.iter collect ds
    | TypD (id, _, insts) -> typs := (id.it, insts) :: !typs
    | _ -> () in
  List.iter collect il;
  let heads_of_typ t =
    let acc = ref [] in
    let rec go t = match t.it with
      | VarT (id, args) ->
        acc := id.it :: !acc;
        List.iter (fun a -> match a.it with TypA t' -> go t' | _ -> ()) args
      | IterT (t', _) -> go t'
      | TupT ps -> List.iter (fun (_, t') -> go t') ps
      | _ -> () in
    go t; !acc in
  let inst_bad inst = (match inst.it with
    | InstD (quants, _, {it = VariantT cases; _}) ->
      variant_indexed quants cases <> [] ||
      List.exists (fun (_, (t, _, _), _) -> case_args_dependent t) cases
    | _ -> false) in
  List.iter (fun (id, insts) ->
    if List.exists inst_bad insts then
      !env_ref.eq_skip <- StringSet.add id !env_ref.eq_skip) !typs;
  let inst_heads inst = (match inst.it with
    | InstD (_, _, {it = VariantT cases; _}) ->
      List.concat_map (fun (_, (t, _, _), _) ->
        List.concat_map heads_of_typ (transform_case_typ t)) cases
    | InstD (_, _, {it = StructT fields; _}) ->
      List.concat_map (fun (_, (t, _, _), _) -> heads_of_typ t) fields
    | InstD (_, _, {it = AliasT t; _}) -> heads_of_typ t) in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (id, insts) ->
      if not (StringSet.mem id !env_ref.eq_skip) &&
         List.exists (fun i -> List.exists (fun h ->
           StringSet.mem h !env_ref.eq_skip) (inst_heads i)) insts
      then begin
        !env_ref.eq_skip <- StringSet.add id !env_ref.eq_skip;
        changed := true
      end) !typs
  done

(* constraints propagate through call graph, fixpoint over functions *)
let compute_fun_needs il =
  let defs = ref [] in
  let rec collect_decds d = match d.it with
    | RecD ds -> List.iter collect_decds ds
    | DecD (id, params, typ, clauses) -> defs := (id, params, typ, clauses) :: !defs
    | _ -> () in
  List.iter collect_decds il;
  let eq_pred p_id e = match e.it with
    | CmpE ((`EqOp | `NeOp), _, e1, _) | MemE (e1, _) -> has_typ p_id e1.note
    | _ -> false in
  let inh_pred p_id e = match e.it with
    | IdxE (e1, _) -> has_typ p_id (elem_typ e1.note)
    | TheE _ -> has_typ p_id e.note
    | _ -> false in
  (* direct needs *)
  List.iter (fun (id, params, typ, clauses) ->
    let eq_set = List.filter_map (fun pp -> match pp.it with
      | TypP x when clauses_need (eq_pred x.it) clauses -> Some x.it
      | _ -> None) params |> StringSet.of_list in
    let inh_set = List.filter_map (fun pp -> match pp.it with
      | TypP x when clauses_need (inh_pred x.it) clauses ||
                    (needs_catch_all clauses && typ_needs_inh_param x.it typ) -> Some x.it
      | _ -> None) params |> StringSet.of_list in
    !env_ref.fun_eq_needs <- StringMap.add id.it eq_set !env_ref.fun_eq_needs;
    !env_ref.fun_inh_needs <- StringMap.add id.it inh_set !env_ref.fun_inh_needs
  ) !defs;
  (* fixpoint over calls *)
  let get m id = Option.value ~default:StringSet.empty (StringMap.find_opt id m) in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (fid, fparams, _, clauses) ->
      let fparam_ids = List.filter_map (fun pp -> match pp.it with
        | TypP x -> Some x.it | _ -> None) fparams in
      if fparam_ids <> [] then begin
        let check_call g gargs =
          match Il.Env.find_opt_def !env_ref.il_env g with
          | None -> ()
          | Some (gparams, _, _) ->
            List.iteri (fun i gp -> match gp.it with
              | TypP pg ->
                let constrained m = StringSet.mem pg.it (get m g.it) in
                (match List.nth_opt gargs i with
                 | Some {it = TypA t; _} ->
                   List.iter (fun x ->
                     if has_typ x t then begin
                       if constrained !env_ref.fun_eq_needs &&
                          not (StringSet.mem x (get !env_ref.fun_eq_needs fid.it)) then begin
                         !env_ref.fun_eq_needs <- StringMap.add fid.it
                           (StringSet.add x (get !env_ref.fun_eq_needs fid.it)) !env_ref.fun_eq_needs;
                         changed := true
                       end;
                       if constrained !env_ref.fun_inh_needs &&
                          not (StringSet.mem x (get !env_ref.fun_inh_needs fid.it)) then begin
                         !env_ref.fun_inh_needs <- StringMap.add fid.it
                           (StringSet.add x (get !env_ref.fun_inh_needs fid.it)) !env_ref.fun_inh_needs;
                         changed := true
                       end
                     end) fparam_ids
                 | _ -> ())
              | _ -> ()) gparams
        in
        let c = { Il.Walk.exists_base_checker with Il.Walk.collect_exp = (fun e ->
          (match e.it with
           | CallE (g, gargs) -> check_call g gargs
           | _ -> ());
          (false, true)) } in
        List.iter (fun cl -> match cl.it with
          | DefD (_, args, e, prems) ->
            List.iter (fun a -> ignore (Il.Walk.collect_arg c a)) args;
            ignore (Il.Walk.collect_exp c e);
            List.iter (fun pr -> ignore (Il.Walk.collect_prem c pr)) prems) clauses
      end
    ) !defs
  done;
  (* concrete instantiations of constrained params need instances *)
  let mark_call g gargs =
    match Il.Env.find_opt_def !env_ref.il_env g with
    | None -> ()
    | Some (gparams, _, _) ->
      List.iteri (fun i gp -> match gp.it with
        | TypP pg ->
          (match List.nth_opt gargs i with
           | Some {it = TypA t; _} ->
             if StringSet.mem pg.it (get !env_ref.fun_eq_needs g.it) then mark_needed `Eq t;
             if StringSet.mem pg.it (get !env_ref.fun_inh_needs g.it) then mark_needed `Inh t
           | _ -> ())
        | _ -> ()) gparams in
  let c = { Il.Walk.exists_base_checker with Il.Walk.collect_exp = (fun e ->
    (match e.it with
     | CallE (g, gargs) -> mark_call g gargs
     | _ -> ());
    (false, true)) } in
  let rec walk_def d = match d.it with
    | RecD ds -> List.iter walk_def ds
    | DecD (_, _, _, clauses) ->
      List.iter (fun cl -> match cl.it with
        | DefD (_, args, e, prems) ->
          List.iter (fun a -> ignore (Il.Walk.collect_arg c a)) args;
          ignore (Il.Walk.collect_exp c e);
          List.iter (fun pr -> ignore (Il.Walk.collect_prem c pr)) prems) clauses
    | RelD (_, _, _, _, rules) ->
      List.iter (fun r -> match r.it with
        | RuleD (_, _, _, e, prems) ->
          ignore (Il.Walk.collect_exp c e);
          List.iter (fun pr -> ignore (Il.Walk.collect_prem c pr)) prems) rules
    | _ -> () in
  List.iter walk_def il

let render_fun_params raw_id params =
  let get m = Option.value ~default:StringSet.empty (StringMap.find_opt raw_id m) in
  let eq_set = get !env_ref.fun_eq_needs in
  let inh_set = get !env_ref.fun_inh_needs in
  String.concat "" (List.map (fun p ->
    " " ^ render_param RHS p ^
    (match p.it with
     | TypP i ->
       (if StringSet.mem i.it eq_set then " {{_ : HasEq " ^ render_id i.it ^ "}}" else "") ^
       (if StringSet.mem i.it inh_set then " {{_ : Inhabited " ^ render_id i.it ^ "}}" else "")
     | _ -> "")) params)

let render_function_def raw_id at params r_typ clauses =
  let id = render_id raw_id in
  let is_proj_func = StringSet.mem raw_id !env_ref.proj_set in
  (* spec fns recurse non-structurally, reduction works, TODO sized types or termination arg *)
  "{-# TERMINATING #-}\n" ^
  id ^ " :" ^ render_fun_params raw_id params ^ " → " ^ render_type RHS r_typ ^ "\n" ^
  String.concat "\n" (List.map (fun clause -> match clause.it with
    | DefD (quants, args, exp, prems) ->
    let (let_prems, others) = List.partition is_let prems in
    assert (List.for_all (fun o -> o.it = ElsePr) others);
    ignore render_prem;
    (* pattern tu^n binds n as list length, bind with lets in body *)
    let rec listn_binders e = (match e.it with
      | IterE (e1, (ListN ({it = VarE n; _}, _), ides)) ->
        let target = (match ides with
          | (_, src) :: _ -> src
          | [] -> e1) in
        (n, target) :: listn_binders e1
      | IterE (e1, _) -> listn_binders e1
      | TupE es -> List.concat_map listn_binders es
      | CaseE (_, e1) -> listn_binders e1
      | _ -> []) in
    (* snoc xs ++ [x] not ctor pattern, match cons and recover with unsnoc-cons *)
    let rec rewrite_snoc e = (match e.it with
      | CatE ({it = VarE xs; _}, {it = ListE [{it = VarE x; _}]; _}) ->
        let el_t = elem_typ e.note in
        let hd = (xs.it ^ "_hd") $ no_region in
        let tl = (xs.it ^ "_tl") $ no_region in
        let e' = CatE (
          ListE [VarE hd $$ no_region % el_t] $$ no_region % e.note,
          VarE tl $$ no_region % e.note) $$ e.at % e.note in
        (e', ["let (" ^ render_id xs.it ^ " , " ^ render_id x.it ^ ") = unsnoc-cons " ^
              render_id hd.it ^ " " ^ render_id tl.it ^ " in "])
      | TupE es ->
        let es', lets = List.split (List.map rewrite_snoc es) in
        ({e with it = TupE es'}, List.concat lets)
      | CaseE (m, e1) ->
        let e1', lets = rewrite_snoc e1 in
        ({e with it = CaseE (m, e1')}, lets)
      | _ -> (e, [])) in
    let args, snoc_lets = List.split (List.map (fun a -> match a.it with
      | ExpA e -> let e', lets = rewrite_snoc e in ({a with it = ExpA e'}, lets)
      | _ -> (a, [])) args) in
    let snoc_lets = List.concat snoc_lets in
    let binders = List.concat_map (fun a -> match a.it with
      | ExpA e -> listn_binders e
      | _ -> []) args in
    (* stray dimension quants, bind to length of first list-typed pattern var *)
    let pattern_vars = (Il.Free.free_list Il.Free.free_arg args).Il.Free.varid in
    let rec first_list_var e = (match e.it with
      | VarE v when (match e.note.it with IterT (_, List) -> true | _ -> false) -> [(v, e)]
      | TupE es -> List.concat_map first_list_var es
      | CaseE (_, e1) -> first_list_var e1
      | IterE (e1, _) -> first_list_var e1
      | _ -> []) in
    let list_vars = List.concat_map (fun a -> match a.it with
      | ExpA e -> first_list_var e | _ -> []) args in
    let rec used_as_bound q e = (match e.it with
      | IterE (e1, (ListN (en, _), ides)) ->
        Il.Free.Set.mem q (Il.Free.free_exp en).Il.Free.varid ||
        used_as_bound q e1 || List.exists (fun (_, e2) -> used_as_bound q e2) ides
      | _ ->
        let c = { Il.Walk.exists_base_checker with Il.Walk.collect_exp = (fun e' ->
          (match e'.it with
           | IterE (_, (ListN (en, _), _)) ->
             (Il.Free.Set.mem q (Il.Free.free_exp en).Il.Free.varid, true)
           | _ -> (false, true))) } in
        Il.Walk.collect_exp c e) in
    let dim_binders = (match list_vars with
      | (lv, _) :: _ ->
        List.filter_map (fun qd -> match qd.it with
          | ExpP (q, t) when
              not (Il.Free.Set.mem q.it pattern_vars) &&
              (used_as_bound q.it exp ||
               (match (reduce_typ_safe !env_ref.il_env t).it with
                | NumT _ -> true | _ -> false)) ->
            Some ("let " ^ render_id q.it ^ " = length " ^ render_id lv.it ^ " in ")
          | _ -> None) quants
      | [] -> []) in
    let string_of_len_lets = String.concat "" (List.map (fun (n, e1) ->
      "let " ^ render_id n.it ^ " = length " ^ parens (render_exp LHS e1) ^ " in ") binders) ^
      String.concat "" dim_binders ^ String.concat "" snoc_lets in
    id ^ render_match_args args ^ " = " ^ string_of_len_lets ^
      wrap_let_prems ~codomain:(render_type RHS r_typ) let_prems (render_exp RHS exp)) clauses
  ) ^
  (if needs_catch_all clauses then
    (* name params so family-typed result can call default helper *)
    "\n" ^ id ^ string_of_list_prefix " " " " get_param_id params ^ " = " ^ render_default_term r_typ
  else "") ^
  if is_proj_func
  then
    "\n\n" ^
    render_coercion (render_single_type id at params) (render_type RHS r_typ) id
  else ""

(* declared-dim iters lose n = |sources| link, emit as explicit premises *)
let collect_dim_constraint_strs exp prems =
  let acc = ref [] in
  let add n src =
    let c = "((length " ^ parens (render_exp RHS src) ^ ") ≡ " ^
            parens (render_exp RHS n) ^ ")" in
    if not (List.mem c !acc) then acc := c :: !acc in
  let hook outer_note body (iter, quants) = (match iter, quants with
    | ListN (n, _), (_ :: _) ->
      List.iter (fun (_, src) -> add n src) quants
    | ListN (n, _), [] ->
      (* annotation-style dim over already-list body, keep length link *)
      (match body with
       | Some b when Il.Eq.eq_typ b.note outer_note -> add n b
       | _ -> ())
    | _ -> ()) in
  let c = { Il.Walk.exists_base_checker with
    Il.Walk.collect_exp = (fun e ->
      (match e.it with IterE (b, ie) -> hook e.note (Some b) ie | _ -> ()); (false, true));
    Il.Walk.collect_prem = (fun p ->
      (match p.it with IterPr (_, ie) -> hook (BoolT $ no_region) None ie | _ -> ()); (false, true)) } in
  ignore (Il.Walk.collect_exp c exp);
  List.iter (fun p -> ignore (Il.Walk.collect_prem c p)) prems;
  List.rev !acc

let render_relation id typ rules =
  "data " ^ id ^ " : " ^ string_of_relation_args typ ^ "Set where\n  " ^
  String.concat "\n  " (List.map (fun rule -> match rule.it with
    | RuleD (rule_id, quants, _, exp, prems) ->
      let letprems, others = List.partition is_let prems in
      let extra = collect_dim_constraint_strs exp prems in
      let prem_strs = extra @ List.map render_prem others in
      let string_prems = string_of_list "\n    " " →\n    " " →\n    " (fun x -> x) prem_strs in
      let forall_quantifiers = string_of_list "∀ " " → " " " (render_quant RHS) quants in
      let conclusion = id ^ " " ^ String.concat " " (List.map (render_exp RHS) (transform_case_tup exp)) in
      render_id rule_id.it ^ " : " ^ forall_quantifiers ^
      wrap_let_prems letprems (string_prems ^ conclusion)
  ) rules)

let render_axiom id params r_typ =
  "postulate " ^ id ^ " : " ^ string_of_list "∀ " " → " " " (render_param RHS) params ^ render_type RHS r_typ

let render_rel_axiom id typ =
  "postulate " ^ id ^ " : " ^ string_of_relation_args typ ^ "Set"

let render_global_declaration id typ exp =
  id ^ " : " ^ render_type RHS typ ^ "\n" ^ id ^ " = " ^ render_exp RHS exp

let has_prems c =
  let only_otherwise_or_let prems =
    match prems with
    | [{it = ElsePr; _}] -> true
    | prems when List.for_all is_let prems -> true
    | _ -> false
  in
  match c.it with
  | DefD (_, _, _, prems) -> prems <> [] && not (only_otherwise_or_let prems)

let is_wf_lemma d =
  match d.it with
  | RelD (id, _, _, _, _) when StringSet.mem id.it !env_ref.wf_lemma_set ->
    true
  | _ -> false

let indent_lines s =
  Str.split (Str.regexp "\n") s |> List.map (fun l -> "  " ^ l) |> String.concat "\n"

(* type family -> Set-valued fn by clauses, variant/record instances get aux type *)
let render_family id params insts =
  let fid = render_id id in
  let aux_name i = fid ^ "-fam" ^ string_of_int i in
  let dispatch i quants args rhs_str =
    fid ^ string_of_list_prefix " " " " (render_arg LHS) args ^ " = " ^ rhs_str ^
    string_of_list_prefix " " " " get_param_id quants ^
    (ignore i; "")
  in
  let aux_defs, clauses = List.mapi (fun i inst ->
    match inst.it with
    | InstD (_, args, {it = AliasT typ; _}) ->
      (None, fid ^ string_of_list_prefix " " " " (render_arg LHS) args ^ " = " ^ render_type RHS typ)
    | InstD (quants, args, {it = VariantT typcases; _}) ->
      (Some (render_variant_typ (aux_name i) quants typcases ^
             render_inhabited_variant id (aux_name i) quants typcases ^
             render_haseq_variant id (aux_name i) quants typcases),
       dispatch i quants args (aux_name i))
    | InstD (quants, args, {it = StructT typfields; _}) ->
      (Some (render_record (aux_name i) quants typfields ^
             render_inhabited_record id (aux_name i) quants typfields ^
             render_haseq_record id (aux_name i) quants typfields),
       dispatch i quants args (aux_name i))
  ) insts |> List.split in
  (* partial families completed with ⊤, default helpers stay total, TODO ⊥-completion with absurd patterns sharper *)
  let catch_all =
    fid ^ String.concat "" (List.map (fun _ -> " _") params) ^ " = ⊤" in
  (* default at symbolic family app needs instance by cases over arg, on demand *)
  let inhabited_instance =
    if not (StringSet.mem id !env_ref.needed_inh) then "" else
    let fun_name = "inh-" ^ fid ^ "-fun" in
    let param_ids = String.concat " " (List.map get_param_id params) in
    let inst_clause inst = (match inst.it with
      | InstD (_, args, {it = AliasT t; _}) ->
        fun_name ^ string_of_list_prefix " " " " (render_arg LHS) args ^
        " = record { default-val = " ^ render_default_term t ^ " }"
      | InstD (_, args, _) ->
        fun_name ^ string_of_list_prefix " " " " (render_arg LHS) args ^
        " = record { default-val = default-val }") in
    (* partial families, cover missing ctor cases so app reduces to ⊤ and tt typechecks, single-param variant only *)
    let last_inst_covers =
      (match List.rev insts with
       | {it = InstD (_, args, _); _} :: _ -> List.for_all is_var_pattern args
       | [] -> false) in
    let helper_catch_all =
      if last_inst_covers then []
      else match params with
        | [{it = ExpP (_, pt); _}] ->
          (match (reduce_typ_safe !env_ref.il_env pt).it with
           | VarT (pt_id, _) ->
             (match Il.Env.find_opt_typ !env_ref.il_env pt_id with
              | Some (_, [{it = InstD (_, _, {it = VariantT ptcases; _}); _}]) ->
                let covered = List.filter_map (fun inst -> match inst.it with
                  | InstD (_, [{it = ExpA {it = CaseE (m, _); _}; _}], _) ->
                    Some (render_mixop (render_id pt_id.it) m)
                  | _ -> None) insts in
                List.filter_map (fun (m, (t, _, _), _) ->
                  let cname = render_mixop (render_id pt_id.it) m in
                  if List.mem cname covered then None
                  else
                    let n = List.length (transform_case_typ t) in
                    let pat = if n = 0 then cname
                      else parens (cname ^ String.concat "" (List.init n (fun _ -> " _"))) in
                    Some (fun_name ^ " " ^ pat ^ " = record { default-val = tt }")
                ) ptcases
              | _ -> [])
           | _ -> [])
        | _ -> [] in
    (* deliberately not an instance, fn-headed target wedges instance search, call helper directly *)
    "\n\n" ^
    fun_name ^ " :" ^ render_params params ^ " → Inhabited " ^ parens (fid ^ " " ^ param_ids) ^ "\n" ^
    String.concat "\n" (List.map inst_clause insts @ helper_catch_all) in
  String.concat "" (List.filter_map (Option.map (fun s -> s ^ "\n\n")) aux_defs) ^
  fid ^ " :" ^ render_params params ^ " → Set\n" ^
  String.concat "\n" (clauses @ [catch_all]) ^
  inhabited_instance

let rec string_of_def in_mutual def =
  let start = comment_parens (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region def.at) ^ "\n" in
  match def.it with
  | TypD (id, _, [{it = InstD (quants, [], {it = AliasT typ; _}); _}]) ->
    start ^ render_typealias (render_id id.it) quants typ
  | TypD (id, _, [{it = InstD (quants, [], {it = StructT typfields; _}); _}]) ->
    start ^ render_record (render_id id.it) quants typfields ^
    render_inhabited_record id.it (render_id id.it) quants typfields ^
    render_haseq_record id.it (render_id id.it) quants typfields
  | TypD (id, _, [{it = InstD (quants, [], {it = VariantT typcases; _}); _}]) ->
    start ^ render_variant_typ (render_id id.it) quants typcases ^
    render_inhabited_variant id.it (render_id id.it) quants typcases ^
    render_haseq_variant id.it (render_id id.it) quants typcases
  | TypD (id, params, ((_ :: _) as insts)) ->
    start ^ render_family id.it params insts
  | DecD (id, [], typ, [{it = DefD ([], [], exp, _); _}]) ->
    start ^ render_global_declaration (render_id id.it) typ exp
  | DecD (id, params, typ, []) ->
    start ^ render_axiom (render_id id.it) params typ
  | DecD (id, params, typ, clauses) when List.exists has_prems clauses ->
    start ^ render_axiom (render_id id.it) params typ
  | DecD (id, params, typ, clauses) ->
    start ^ render_function_def id.it id.at params typ clauses
  | RelD (id, _, _, typ, []) ->
    start ^ render_rel_axiom (render_id id.it) typ
  | RelD (id, _, _, _, [rule]) when is_wf_lemma def ->
    start ^ render_wfness_func_lemma (render_id id.it) rule
  | RelD (id, _, _, typ, rules) ->
    start ^ render_relation (render_id id.it) typ rules
  (* Mutual recursion *)
  | RecD defs -> (match defs with
    | [] -> ""
    | _ when List.for_all is_wf_lemma defs ->
      String.concat "\n\n" (List.map (string_of_def in_mutual) defs)
    | [d] -> string_of_def in_mutual d
    | _ when in_mutual -> String.concat "\n\n" (List.map (string_of_def true) defs)
    | _ ->
      let rec group_ids d = (match d.it with
        | TypD (id, _, _) -> [id.it]
        | RecD ds -> List.concat_map group_ids ds
        | _ -> []) in
      let saved = !env_ref.cur_group in
      !env_ref.cur_group <- StringSet.of_list (List.concat_map group_ids defs);
      let rendered = String.concat "\n\n" (List.map (fun d -> indent_lines (string_of_def true d)) defs) in
      !env_ref.cur_group <- saved;
      "mutual\n" ^ rendered
    )
  | _ -> error def.at ("Unsupported def: " ^ Il.Print.string_of_def def)

let exported_string = {|{-# OPTIONS -WnoUnreachableClauses #-}
{- Preamble -}
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _>_; _≥_; _^_; _⊔_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_)
open import Agda.Builtin.Nat using (_+_; _*_) renaming (_-_ to _–_)
open import Data.Nat using () renaming (_/_ to _/′_; _%_ to _%′_)
open import Data.String using (String) renaming (_==_ to eqString)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mapMaybe; zipWith to maybeZipWith)
open import Data.List using (List; []; _∷_; fromMaybe; length; _++_; replicate; take; drop; zip; zipWith; map; upTo)
open import Data.Bool.ListAction using (any)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)

{- Type ascription -}
as : (A : Set) → A → A
as A x = x

{- Truth of booleans -}
is-true : Bool → Set
is-true b = b ≡ true

{- Boolean operations -}
_impliesᵇ_ : Bool → Bool → Bool
a impliesᵇ b = not a ∨ b

_=ᵇ_ : Bool → Bool → Bool
true =ᵇ b = b
false =ᵇ b = not b

{- Default values -}
record Inhabited (A : Set) : Set where
  field default-val : A
open Inhabited {{...}}

instance
  Inh-ℕ : Inhabited ℕ
  Inh-ℕ = record { default-val = 0 }

  Inh-Bool : Inhabited Bool
  Inh-Bool = record { default-val = false }

  Inh-⊤ : Inhabited ⊤
  Inh-⊤ = record { default-val = tt }

  Inh-String : Inhabited String
  Inh-String = record { default-val = "" }

  Inh-List : {A : Set} → Inhabited (List A)
  Inh-List = record { default-val = [] }

  Inh-Maybe : {A : Set} → Inhabited (Maybe A)
  Inh-Maybe = record { default-val = nothing }

  Inh-× : {A B : Set} → {{Inhabited A}} → {{Inhabited B}} → Inhabited (A × B)
  Inh-× = record { default-val = (default-val , default-val) }

{- Boolean equality -}
record HasEq (A : Set) : Set where
  field _=?_ : A → A → Bool
open HasEq {{...}}

_≠?_ : {A : Set} → {{HasEq A}} → A → A → Bool
x ≠? y = not (x =? y)

eq-List-fun : {A : Set} → {{HasEq A}} → List A → List A → Bool
eq-List-fun [] [] = true
eq-List-fun (x ∷ xs) (y ∷ ys) = (x =? y) ∧ eq-List-fun xs ys
eq-List-fun _ _ = false

eq-Maybe-fun : {A : Set} → {{HasEq A}} → Maybe A → Maybe A → Bool
eq-Maybe-fun nothing nothing = true
eq-Maybe-fun (just x) (just y) = x =? y
eq-Maybe-fun _ _ = false

instance
  Eq-ℕ : HasEq ℕ
  Eq-ℕ = record { _=?_ = _≡ᵇ_ }

  Eq-Bool : HasEq Bool
  Eq-Bool = record { _=?_ = _=ᵇ_ }

  Eq-String : HasEq String
  Eq-String = record { _=?_ = eqString }

  Eq-List : {A : Set} → {{HasEq A}} → HasEq (List A)
  Eq-List = record { _=?_ = eq-List-fun }

  Eq-Maybe : {A : Set} → {{HasEq A}} → HasEq (Maybe A)
  Eq-Maybe = record { _=?_ = eq-Maybe-fun }

  Eq-× : {A B : Set} → {{HasEq A}} → {{HasEq B}} → HasEq (A × B)
  Eq-× = record { _=?_ = λ where (a , b) (a' , b') → (a =? a') ∧ (b =? b') }

_∈ᵇ_ : {A : Set} → {{HasEq A}} → A → List A → Bool
x ∈ᵇ xs = any (λ y → x =? y) xs

{- Boolean number comparisons -}
_<?_ : ℕ → ℕ → Bool
a <? b = a <ᵇ b

_>?_ : ℕ → ℕ → Bool
a >? b = b <ᵇ a

_≤?_ : ℕ → ℕ → Bool
a ≤? b = a ≤ᵇ b

_≥?_ : ℕ → ℕ → Bool
a ≥? b = b ≤ᵇ a

{- Arithmetic operations (total: division by zero yields zero) -}
_/_ : ℕ → ℕ → ℕ
a / zero = 0
a / suc b = a /′ suc b

_%_ : ℕ → ℕ → ℕ
a % zero = 0
a % suc b = a %′ suc b

{- Numeric type coercions -}
record Coerce (A B : Set) : Set where
  field coerce : A → B
open Coerce {{...}}

instance
  Coerce-ℕ : Coerce ℕ ℕ
  Coerce-ℕ = record { coerce = λ n → n }

  Coerce-Maybe : {A B : Set} → {{Coerce A B}} → Coerce (Maybe A) (Maybe B)
  Coerce-Maybe = record { coerce = mapMaybe coerce }

  Coerce-List : {A B : Set} → {{Coerce A B}} → Coerce (List A) (List B)
  Coerce-List = record { coerce = map coerce }

{- Record composition -}
record HasAppend (A : Set) : Set where
  field append : A → A → A
open HasAppend {{...}}

_⧺_ : {A : Set} → {{HasAppend A}} → A → A → A
_⧺_ = append
infixr 5 _⧺_

maybe-append : {A : Set} → Maybe A → Maybe A → Maybe A
maybe-append (just x) _ = just x
maybe-append nothing y = y

instance
  Append-List : {A : Set} → HasAppend (List A)
  Append-List = record { append = _++_ }

  Append-Maybe : {A : Set} → HasAppend (Maybe A)
  Append-Maybe = record { append = maybe-append }

  Append-ℕ : HasAppend ℕ
  Append-ℕ = record { append = _+_ }

{- List operations -}
slice : {A : Set} → List A → ℕ → ℕ → List A
slice xs i n = take n (drop i xs)

slice-update : {A : Set} → List A → ℕ → ℕ → List A → List A
slice-update xs i n u = take i xs ++ take n u ++ drop (i + n) xs

modify : {A : Set} → List A → ℕ → (A → A) → List A
modify (x ∷ xs) zero    f = f x ∷ xs
modify (x ∷ xs) (suc n) f = x ∷ modify xs n f
modify [] _ _ = []

mkseq : {A : Set} → (ℕ → A) → ℕ → List A
mkseq f n = map f (upTo n)

unsnoc-cons : {A : Set} → A → List A → (List A × A)
unsnoc-cons x [] = ([] , x)
unsnoc-cons x (y ∷ ys) = let (zs , z) = unsnoc-cons y ys in ((x ∷ zs) , z)

zipWith₃ : {A B C D : Set} → (A → B → C → D) → List A → List B → List C → List D
zipWith₃ f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zipWith₃ f xs ys zs
zipWith₃ _ _ _ _ = []

maybeZipWith₃ : {A B C D : Set} → (A → B → C → D) → Maybe A → Maybe B → Maybe C → Maybe D
maybeZipWith₃ f (just x) (just y) (just z) = just (f x y z)
maybeZipWith₃ _ _ _ _ = nothing

{- Total lookup and unwrapping (default values off-domain; the generated
   side conditions guarantee on-domain use) -}
_[_]! : {A : Set} → {{Inhabited A}} → (xs : List A) → (i : ℕ) → A
([] [ _ ]!) = default-val
((x ∷ xs) [ zero ]!)  = x
((x ∷ xs) [ suc i ]!) = xs [ i ]!

unwrap! : {A : Set} → {{Inhabited A}} → Maybe A → A
unwrap! (just a) = a
unwrap! nothing = default-val

{- Iterated premises (inductive: length-forcing, with induction principles) -}
Forall : {A : Set} → (A → Set) → List A → Set
Forall = All

Forall₂ : {A B : Set} → (A → B → Set) → List A → List B → Set
Forall₂ = Pointwise

data Forall₃ {A B C : Set} (R : A → B → C → Set) :
             List A → List B → List C → Set where
  []  : Forall₃ R [] [] []
  _∷_ : ∀ {x y z xs ys zs} → R x y z → Forall₃ R xs ys zs →
        Forall₃ R (x ∷ xs) (y ∷ ys) (z ∷ zs)

Foralli : {A : Set} → (ℕ → A → Set) → List A → Set
Foralli f xs = Pointwise f (upTo (length xs)) xs

holds-upto : (ℕ → Set) → ℕ → Set
holds-upto P n = All P (upTo n)

|}

let rec filter_def def =
  match def.it with
  | GramD _ | HintD _ -> None
  | RecD defs -> Some {def with it = RecD (List.filter_map filter_def defs) }
  | _ -> Some def

let is_tf_hint h = h.hintid.it = Middlend.Typefamilyremoval.type_family_hint_id
let is_proj_hint h = h.hintid.it = Middlend.Uncaseremoval.uncase_proj_hint_id
let is_wf_hint h = h.hintid.it = Middlend.Undep.wf_hint_id
let is_wf_func_hint h = h.hintid.it = Middlend.Undep.wf_func_id
let is_wf_rel_hint h = h.hintid.it = Middlend.Undep.wf_rel_id

let rec register_hints env def =
  match def.it with
  | HintD { it = TypH (id, hints); _} when List.exists is_tf_hint hints ->
    env.tf_set <- StringSet.add id.it env.tf_set
  | HintD { it = DecH (id, hints); _} when List.exists is_proj_hint hints ->
    env.proj_set <- StringSet.add id.it env.proj_set
  | HintD { it = RelH (id, hints); _} when List.exists is_wf_func_hint hints ->
    env.wf_lemma_set <- StringSet.add id.it env.wf_lemma_set
  | HintD { it = RelH (id, hints); _} when List.exists is_wf_rel_hint hints ->
    env.wf_lemma_set <- StringSet.add id.it env.wf_lemma_set
  | HintD { it = RelH (rel_id, hints); _} when List.exists is_wf_hint hints ->
    begin match (List.find_opt is_wf_hint hints) with
    | Some {hintexp = { it = El.Ast.VarE (typ_id, _); _}; _} ->
      env.typ_to_wf_map <- StringMap.add typ_id.it rel_id.it env.typ_to_wf_map
    | _ -> ()
    end
  | RecD defs -> List.iter (register_hints env) defs
  | _ -> ()

let string_of_script (il : script) =
  (* printing evaluates types, disable clause-skip on stuck matches *)
  Il.Eval.conservative_matches := true;
  env_ref := new_env ();
  !env_ref.il_env <- Il.Env.env_of_script il;
  List.iter (register_hints !env_ref) il;
  let il' = Disamb.transform il in
  (* re-derive env from renamed script so reduce_typ can evaluate case atoms *)
  !env_ref.il_env <- Il.Env.env_of_script il';
  collect_needed_script il';
  compute_eq_ineligible il';
  compute_fun_needs il';
  exported_string ^
  "{- Generated Code -}\n\n" ^
  String.concat "\n\n" (List.filter_map filter_def il' |> List.map (string_of_def false)) ^ "\n"
