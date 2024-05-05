(* type term =
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

(* Pretty printer *)

let var_prec = 3
let app_prec = 2
let abs_prec = 1

let rec pretty_term_helper_with_sub t prec = match t with
  | Var { orig_name = _; name = name; sub = NoSub } -> Utils.surround_prec var_prec prec name
  | Var { orig_name = _; name = name; sub = SubTerm t } -> Utils.surround_prec var_prec prec (name ^ "[" ^ name ^ "<= " ^ pretty_term_with_sub t ^ "]")
  | Var { orig_name = _; name = name; sub = SubValue t } -> Utils.surround_prec var_prec prec (name ^ "[" ^ name ^ "<- " ^ pretty_term_with_sub t ^ "]")
  | Var { orig_name = _; name = _; sub = Copy _ } -> raise InvalidTerm
  | Abs {v; body} -> Utils.surround_prec abs_prec prec ("λ" ^ v.name ^ ". " ^ pretty_term_helper_with_sub body abs_prec)
  | App {head; arg} -> Utils.surround_prec app_prec prec (pretty_term_helper_with_sub head app_prec ^ " " ^ pretty_term_helper_with_sub arg (app_prec + 1))

and pretty_term_with_sub t = pretty_term_helper_with_sub t 0

let rec pretty_term_helper t prec = match t with
  | Var { orig_name = _; name = name; sub = _ } -> Utils.surround_prec var_prec prec name
  | Abs {v; body} -> Utils.surround_prec abs_prec prec ("λ" ^ v.name ^ ". " ^ pretty_term_helper body abs_prec)
  | App {head; arg} -> Utils.surround_prec app_prec prec (pretty_term_helper head app_prec ^ " " ^ pretty_term_helper arg (app_prec + 1))

and pretty_term t = pretty_term_helper t 0




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
and state = term * stack * chain * bool

let step (s : state) = match s with
  | Var vref, stack, chain, eval_done ->
      (match vref.sub with
        | NoSub -> raise (UnboundVariable vref.name)
        | SubTerm t -> (t, [], (vref, stack) :: chain, eval_done)
        | SubValue v -> (rename_term v, stack, chain, eval_done)
        | Copy _ -> raise InvalidTerm)
  | Abs _ as value, [], [], _ -> (value, [], [], true) (* Evaluation is over *)
  | Abs _ as value, [], (vref, stack) :: chain, eval_done ->
      (vref.sub <- SubValue value;
       (Var vref, stack, chain, eval_done))
  | Abs { v; body }, arg :: args, chain, eval_done -> 
      (v.sub <- SubTerm arg;
       (body, args, chain, eval_done))
  | App { head; arg }, args, chain, eval_done ->
      (head, arg :: args, chain, eval_done)

let pretty_stack s =
    let rec pretty_stack_internal = function
      | [] -> ""
      | t :: ts -> pretty_term t ^ ", " ^ pretty_stack_internal ts
    in
    "[" ^ pretty_stack_internal s ^ "]"

let rec pretty_chain = function
  | [] -> ""
  | (v, s) :: cs -> "(" ^ v.name ^ ", " ^ pretty_stack s ^ "), " ^ pretty_chain cs

let print_state (t, s, c, eval_done) = 
    Printf.printf "CURRENT STATE:\n\tTERM: %s\n\tSTACK: %s\n\tCHAIN: %s\n\tEVAL DONE: %b\n" (pretty_term_with_sub t) (pretty_stack s) (pretty_chain c) eval_done

(* Aggiungi il print a ogni step *)
let rec eval = function
  | (value, [], [], true) -> value (* Evaluation is over *)
  | state -> let next_state = step state in print_state next_state; eval next_state

let run t = 
  let s = (t, [], [], false) in
  print_state s;
  eval s
*)
