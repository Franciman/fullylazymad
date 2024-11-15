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
  | Copy of var_ref

exception UnboundVariable of string
exception InvalidTerm

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

let make_fresh_var (orig_name: string) = 
  { orig_name = orig_name; name = Utils.gen_fresh_name orig_name; sub = NoSub }

let rec rename_term (t: term) = match t with
  | Var {orig_name = _; name = _; sub = Copy v} -> Var v
  | Var _ -> t
  | Abs { v; body } ->
      let fresh_v = make_fresh_var v.orig_name in
      v.sub <- Copy fresh_v;
      let renamed_body = rename_term body in
      v.sub <- NoSub; (* inutile; però mantiene l'invariante *)
      Abs { v = fresh_v; body = renamed_body }
  | App { head; arg } -> 
      let new_head = rename_term head in
      let new_arg = rename_term arg in
      App { head = new_head; arg = new_arg }


type stack = term list
and chain = (var_ref * stack) list 
and state = term * stack * chain * bool * int

let step (s : state) = match s with
  | Var vref, stack, chain, eval_done, betas ->
      (match vref.sub with
        | NoSub -> raise (UnboundVariable vref.name)
        | SubTerm t -> (t, [], (vref, stack) :: chain, eval_done, betas)
        | SubValue v -> (rename_term v, stack, chain, eval_done, betas)
        | Copy _ -> raise InvalidTerm)
  | Abs _ as value, [], [], _, betas -> (value, [], [], true, betas) (* Evaluation is over *)
  | Abs _ as value, [], (vref, stack) :: chain, eval_done, betas ->
      (vref.sub <- SubValue value;
       (Var vref, stack, chain, eval_done, betas))
  | Abs { v; body }, arg :: args, chain, eval_done, betas ->
      (v.sub <- SubTerm arg;
       (body, args, chain, eval_done, betas + 1))
  | App { head; arg }, args, chain, eval_done, betas ->
      (head, arg :: args, chain, eval_done, betas)
      
      
(* Pretty printer *)

let var_prec = 3
let app_prec = 2
let abs_prec = 1

let rec pretty_term_helper t prec = match t with
  | Var { orig_name = _; name = name; sub = _ } -> Utils.surround_prec var_prec prec name
  | Abs {v; body} -> Utils.surround_prec abs_prec prec ("λ" ^ v.name ^ ". " ^ pretty_term_helper body abs_prec)
  | App {head; arg} -> Utils.surround_prec app_prec prec (pretty_term_helper head app_prec ^ " " ^ pretty_term_helper arg (app_prec + 1))

and pretty_term t = pretty_term_helper t 0

let rec extract_environment_helper acc t = match t with
  | Var v -> (match v.sub with
               | NoSub -> acc
               | SubTerm t | SubValue t ->
                  (let entry = (v.name, v.sub, v) in
                   (* Remove this substitution, to avoid duplicates. We shall restore it later *)
                   v.sub <- NoSub;
                   entry :: extract_environment_helper acc t)
               | Copy _ -> raise InvalidTerm)
  | Abs a -> extract_environment_helper acc a.body
  | App a -> extract_environment_helper (extract_environment_helper acc a.head) a.arg

and extract_environment (t, s) =
  let env = List.fold_left extract_environment_helper [] (t :: s) in
  (* Now, we restore all vrefs' substitutions to their old value and just return the pair name, sub*)
  List.map (fun (name, sub, vref) -> vref.sub <- sub; (name, sub)) env



let pretty_stack s = String.concat " " (List.map (fun t -> pretty_term_helper t app_prec) s)

let pretty_chain c =
  let pretty_chain_helper (v, s) = Printf.sprintf "\t\tTerm: <%s> %s" v.name (pretty_stack s) in
  String.concat "\n" (List.map pretty_chain_helper c)

let pretty_sub name sub = match sub with
  | NoSub -> ""
  | SubTerm t -> "[" ^ name ^ " <-- " ^ pretty_term t ^ "]"
  | SubValue t -> "[" ^ name ^ " <-- " ^ pretty_term t ^ " / value" ^ "]"
  | Copy _ -> raise InvalidTerm

let rec pretty_env env = match env with
  | [] -> ""
  | (name, sub) :: vrefs -> pretty_sub name sub ^ pretty_env vrefs

let print_state logger (t, s, c, eval_done, betas) =
  Logger.log logger Logger.EvalTrace (lazy (
      let env = extract_environment (t, s) in
      Printf.sprintf "Current state:\n\tEval done: %b\n\tBetas: %d\n\tTerm: <%s> %s\n\tEnv: %s\n\tChain:\n%s" eval_done betas (pretty_term t) (pretty_stack s) (pretty_env env) (pretty_chain c)
  ))

(* Aggiungi il print a ogni step *)
let rec eval logger = function
  | (value, [], [], true, betas) ->
      (Logger.log logger Logger.Summary (lazy (Printf.sprintf "Number of betas: %d\n" betas));
       value) (* Evaluation is over *)
  | state -> let next_state = step state in print_state logger next_state; eval logger next_state

let run logger t =
  let s = (t, [], [], false, 0) in
  print_state logger s;
  eval logger s
