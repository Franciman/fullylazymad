type term =
    Var of var_ref
  | Abs of { v : var_ref; body : term }
  | App of { head : term; arg : term }

(* We also store the original name to be used as basis for generating fresh names *)
and var_ref = { orig_name : string; name : string; mutable sub : sub }
and sub =
    NoSub
  | SubTerm of term
  | SubValue of term
  | SubSkel of term
  | InsideSub
  | Copy of var_ref
  | Uplink of marked_term
and
marked_term =
    MVar of { mutable taken: bool; vref: var_ref; mutable parent: marked_term option }
  | MAbs of { mutable taken: bool; vref: var_ref; mutable occurrences: marked_term list; body: marked_term; mutable parent: marked_term option }
  | MApp of { mutable taken: bool; head: marked_term; arg: marked_term; mutable parent: marked_term option }

exception UnboundVariable of string
exception InvalidTerm

let make_fresh_var (orig_name: string) = 
  { orig_name = orig_name; name = Utils.gen_fresh_name orig_name; sub = NoSub }

  
(* Skeleton extraction *)
let set_parent mt p = match mt with
  | MVar v -> v.parent <- p
  | MAbs a -> a.parent <- p
  | MApp a -> a.parent <- p
  
(* Convert from term to marked_term *)
let rec compute_occurrences mt = match mt with
  | MVar v as var -> (match v.vref.sub with
                       | Uplink (MAbs a) -> a.occurrences <- var :: a.occurrences
                       | _ -> ())
  | MAbs a -> compute_occurrences a.body; a.vref.sub <- NoSub
  | MApp a -> compute_occurrences a.head; compute_occurrences a.arg

let rec blackmark_helper (t: term) : marked_term = match t with
  | Var v -> MVar { taken = false; vref = v; parent = None }
  | Abs a ->
     let new_body = blackmark_helper a.body in
     let res =
       MAbs { taken = false;
              vref = a.v;
              body = new_body;
              occurrences = [];
              parent = None } in
     set_parent new_body (Some res);
     a.v.sub <- Uplink res;
     res
  | App a ->
     let new_head = blackmark_helper a.head in
     let new_arg = blackmark_helper a.arg in
     let res =
       MApp { taken = false;
              head = new_head;
              arg = new_arg;
              parent = None } in
     set_parent new_head (Some res);
     set_parent new_arg (Some res);
     res
                           
and blackmark t = let res = blackmark_helper t in compute_occurrences res; res

let rec mark_skeleton =
 function
  | None -> ()
  | Some (MVar v) -> (v.taken <- true; mark_skeleton v.parent)
  | Some (MAbs a) ->
      if not a.taken
      then (a.taken <- true;
            List.iter (fun v -> mark_skeleton (Some v)) a.occurrences;
            mark_skeleton a.parent)
  | Some (MApp a) ->
      if not a.taken
      then (a.taken <- true; mark_skeleton a.parent)
      
(* Extract flesh and unmark term *)
let rec unmark mt = match mt with
  | MVar v -> Var v.vref
  | MAbs a -> Abs { v = a.vref; body = unmark a.body }
  | MApp a -> App { head = unmark a.head; arg = unmark a.arg }

let rec extract_flesh mt = match mt with
  | MVar v -> Var v.vref
  | MAbs { taken = false; _}
  | MApp { taken = false; _} ->
     let fresh_vref = make_fresh_var "p" in
     fresh_vref.sub <- SubTerm (unmark mt);
     Var fresh_vref
  | MAbs a -> Abs { v = a.vref; body = extract_flesh a.body }
  | MApp a -> App { head = extract_flesh a.head; arg = extract_flesh a.arg }

let extract_skeleton t = match t with
  | Abs _ ->
     let marked_term = blackmark t in
     mark_skeleton (Some marked_term);
     extract_flesh marked_term
  | Var _ | App _ -> raise InvalidTerm

(* Convert a Syntax_tree.term in a term *)

let rec scope_checker env (t: Syntax_tree.term): term =
  match t with
    | Var v -> (match List.assoc_opt v env with
                  | Some vref -> Var vref
                  | None -> raise (UnboundVariable v))
    | Abs (v, body) ->
       (let vref: var_ref = { orig_name = v; name = v; sub = NoSub } in
        Abs { v = vref; body = scope_checker ((v, vref) :: env) body })
    | App (head, arg) -> App { head = scope_checker env head; arg = scope_checker env arg }

let scope_check t = scope_checker [] t

(* Interpreter *)

let rec rename_term (t: term) = match t with
  | Var {orig_name = _; name = _; sub = Copy v} -> Var v
  | Var _ -> t
  | Abs { v; body } ->
      let fresh_v = make_fresh_var v.orig_name in
      v.sub <- Copy fresh_v;
      let renamed_body = rename_term body in
      v.sub <- NoSub;
      Abs { v = fresh_v; body = renamed_body }
  | App { head; arg } -> 
      let new_head = rename_term head in
      let new_arg = rename_term arg in
      App { head = new_head; arg = new_arg }
      
type stack = term list
and chain = (var_ref * stack) list 
and state = term * stack * chain

(* Pretty printer *)

let var_prec = 3
let app_prec = 2
let abs_prec = 1

let rec pretty_term_helper t prec = match t with
  | Var { orig_name = _; name = name; sub = _ } -> Utils.surround_prec var_prec prec name
  | Abs {v; body} -> Utils.surround_prec abs_prec prec ("λ" ^ v.name ^ "." ^ pretty_term_helper body abs_prec)
  | App {head; arg} -> Utils.surround_prec app_prec prec (pretty_term_helper head app_prec ^ "" ^ pretty_term_helper arg (app_prec + 1))

and pretty_term t = pretty_term_helper t 0

let extract_environment ~avoid s =
 let rec extract_environment_helper acc t = match t with
  | Var v -> (match v.sub with
               | _ when List.exists (fun (_,_,v') -> v==v') avoid -> acc
               | NoSub -> acc
               | SubTerm t | SubValue t | SubSkel t ->
                  let entry = (v.name, v.sub, v) in
                  extract_environment_helper (entry::(List.filter (fun (_,_,v') -> v!=v') acc)) t
               | Copy _ | Uplink _ | InsideSub -> raise InvalidTerm)
  | Abs a -> extract_environment_helper acc a.body
  | App a -> extract_environment_helper (extract_environment_helper acc a.head) a.arg
 in
  List.rev (List.fold_left (extract_environment_helper) [] s)


let pretty_stack s = String.concat ":" (List.map (fun t -> pretty_term_helper t app_prec) s)

let pretty_sub name sub = match sub with
  | NoSub -> ""
  | SubTerm t -> "[" ^ name ^ "←" ^ pretty_term t ^ "]ₜ"
  | SubValue t -> "[" ^ name ^ "←" ^ pretty_term t ^ "]ₗ"
  | SubSkel t -> "[" ^ name ^ "←" ^ pretty_term t ^ "]ₛ"
  | InsideSub | Copy _ | Uplink _ -> raise InvalidTerm

let pretty_env env = String.concat ":" (List.map (fun (name,sub,_) -> pretty_sub name sub) env)
  

let pretty_chain ~avoid c =
  let pretty_chain_helper ~avoid (v, s) = 
    let avoid = (v.name,v.sub,v)::avoid in
    let env = extract_environment ~avoid s in
    env@avoid,Printf.sprintf "(%s,%s,%s)"  v.name (pretty_stack s) (pretty_env env) in
  let _,l = List.fold_left (fun (avoid,l) ci -> let avoid,i = pretty_chain_helper ~avoid ci in avoid,i::l) (avoid,[]) c  in
  String.concat ":" l


let print_state logger trans (t, s, c) =
  Logger.log logger Logger.EvalTrace (lazy (
    let env = extract_environment ~avoid:[] (t::s) in
    Printf.sprintf "%s\t\027[31m%s\027[0m|%s|%s|\027[32m%s\027[0m" trans (pretty_chain ~avoid:env c) (pretty_term t) (pretty_stack s) (pretty_env env)
  ))


let step : state -> string * state =
 function
  | App { head; arg }, args, chain ->
      "sea₁ ",(head, arg :: args, chain)
  | Abs { v; body }, arg :: args, chain ->
      v.sub <- SubTerm arg;
      "β",(body, args, chain)
  | Var ({sub=SubTerm t; _} as vref), stack, chain ->
      vref.sub <- InsideSub;
      "sea₂",(t, [], (vref, stack) :: chain)
  | Var ({sub=SubValue v; _} as vref), _stack, _chain as s ->
      let skel = extract_skeleton v in
      vref.sub <- SubSkel skel;
      "sk",s
  | Var {sub=SubSkel v; _}, stack, chain ->
      "ss",(rename_term v, stack, chain)
  | Abs _ as value, [], (vref, stack) :: chain ->
      vref.sub <- SubValue value;
      "sea₃",(Var vref, stack, chain)
  | Abs _, [], [] ->
     assert false (* stepping over a normal term *)
  | Var {sub=NoSub; name; _}, _stack, _chain ->
     raise (UnboundVariable name)
  | Var {sub=(Uplink _ | Copy _ | InsideSub); _}, _stack, _chain ->
     raise InvalidTerm

let rec eval logger betas =
 function
  | (Abs _ as value, [], []) ->
      (* Normal form reached *)
      Logger.log logger Logger.Summary (lazy (Printf.sprintf "Number of betas: %d\n" betas));
      value
  | state ->
     let trans,next_state = step state in
     print_state logger ("→"^trans) next_state;
     eval logger (if trans="β" then betas+1 else betas) next_state

let run logger t =
  let s = (t, [], []) in
  print_state logger "" s;
  eval logger 0 s
