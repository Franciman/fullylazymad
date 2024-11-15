type term =
    Var of { mutable vref: var_ref; mutable parent: term option }
  | Abs of { vref: var_ref; body: term; mutable parent: term option }
  | App of { mutable head: term; arg: term; mutable parent: term option }
and var_ref = { orig_name: string; name: string; mutable sub: sub; mutable occurrences: term list }
and sub =
    NoSub
  | SubTerm of term
  | SubValue of term
  | Copy of var_ref
and state = {
  mutable pc: term;
  (* Terms in the chain are only of type Var *)
  mutable chain: term list;
  mutable eval_done: bool;
  mutable betas: int;
}

exception UnboundVariable of string
exception InvalidTerm

let term_parent = function
  | Var t -> t.parent
  | Abs t -> t.parent
  | App t -> t.parent

let set_term_parent t new_parent = match t with
  | Var t -> (t.parent <- new_parent)
  | Abs t -> (t.parent <- new_parent)
  | App t -> (t.parent <- new_parent)

let set_term_child t child = match t with
  | Var _ -> raise InvalidTerm
  | Abs _ -> raise InvalidTerm
  | App a -> (a.head <- child)

let set_parent_child t child = match t with
  | None -> ()
  | Some t -> set_term_child t child
  
let set_var_vref t new_vref = match t with
  | Var v -> (v.vref <- new_vref)
  | Abs _ | App _ -> raise InvalidTerm

let add_to_chain o ts = match o with
  | None -> ts
  | Some t -> t :: ts

(* Convert a Syntax_tree.term in a term *)

let rec scope_checker env (t: Syntax_tree.term) (parent: term option): term =
   match t with
     | Var v -> (match List.assoc_opt v env with
                  | Some vref -> (let res = Var { vref; parent } in
                                  vref.occurrences <- res :: vref.occurrences;
                                  res)
                  | None -> raise (UnboundVariable v))
    | Abs (v, body) ->
       let vref: var_ref = { orig_name = v; name = v; sub = NoSub; occurrences = [] } in
       let b = scope_checker ((v, vref) :: env) body None in
       let res = Abs { vref = vref; body = b; parent = parent } in
       set_term_parent b (Some res);
       res
    | App (head, arg) ->
       let h = scope_checker env head None in
       let a = scope_checker env arg None in
       let res = App { head = h; arg = a; parent = parent} in
       set_term_parent h (Some res);
       set_term_parent a (Some res);
       res

let scope_check t = scope_checker [] t None


(* Interpreter *)

let make_fresh_var (orig_name: string) = 
  { orig_name = orig_name; name = Utils.gen_fresh_name orig_name; sub = NoSub; occurrences = [] }

let rec rename_term = function
  | Var v as var -> 
      (match v.vref.sub with
         | Copy v_new ->
             (let res = Var { vref = v_new; parent = v.parent } in
              v_new.occurrences <- res :: v_new.occurrences;
              res)
         | _          -> var)
  | Abs a ->
      let fresh_v = make_fresh_var a.vref.orig_name in
      a.vref.sub <- Copy fresh_v;
      let renamed_body = rename_term a.body in
      a.vref.sub <- NoSub;
      let res = Abs { vref = fresh_v; body = renamed_body; parent = a.parent } in
      set_term_parent renamed_body (Some res);
      res

  | App a ->
      let renamed_head = rename_term a.head in
      let renamed_arg = rename_term a.arg in
      let res = App { head = renamed_head; arg = renamed_arg; parent = a.parent } in
      set_term_parent renamed_head (Some res);
      set_term_parent renamed_arg (Some res);
      res

let step (s: state) = match s.pc with
  | Var { vref; parent } as var -> 
     (match vref.sub with
       | NoSub -> raise (UnboundVariable vref.name)
       | SubTerm t -> 
           (s.pc <- t;
            s.chain <- var :: s.chain)
       | SubValue v ->
           (* Make a renamed copy of v *)
           (let renamed_v = rename_term v in
            set_term_parent renamed_v parent;
            set_parent_child parent renamed_v;
            s.pc <- renamed_v)
       | Copy _ -> raise InvalidTerm)

  | Abs a as value -> 
      (match a.parent with
         | Some (Var _) | Some (Abs _) -> raise InvalidTerm
         | Some (App app) ->
             (set_term_parent a.body app.parent;
              set_parent_child app.parent a.body;
              set_term_parent app.arg None;
              a.vref.sub <- SubTerm app.arg;
              s.betas <- s.betas + 1;
              s.pc <- a.body)
         | None -> 
             (match s.chain with
                | [] -> (s.eval_done <- true) (* Evaluation is over *)
                | var :: chain -> 
                    (match var with
                      | Var { vref; _ } ->
                            (vref.sub <- SubValue value;
                             s.chain <- chain;
                             s.pc <- var)
                      | Abs _ | App _ -> raise InvalidTerm)))

  | App a -> (s.pc <- a.head)
        
(* Pretty printer *)

let var_prec = 3
let app_prec = 2
let abs_prec = 1

let rec pretty_term_helper t prec = match t with
  | Var { vref; _ } -> Utils.surround_prec var_prec prec vref.name
  | Abs {vref; body; _} -> Utils.surround_prec abs_prec prec ("λ" ^ vref.name ^ ". " ^ pretty_term_helper body abs_prec)
  | App {head; arg; _} -> Utils.surround_prec app_prec prec (pretty_term_helper head app_prec ^ " " ^ pretty_term_helper arg (app_prec + 1))

and pretty_term t = pretty_term_helper t 0

let rec pretty_deep_term_helper t prec = match t with
  | Var { vref; _ } -> (match vref.sub with
                                    | NoSub -> Utils.surround_prec var_prec prec vref.name
                                    | SubTerm t -> pretty_deep_term_helper t prec
                                    | SubValue t -> pretty_deep_term_helper t prec
                                    | Copy _ -> raise InvalidTerm)
  | Abs {vref; body; _} -> Utils.surround_prec abs_prec prec ("λ" ^ vref.name ^ ". " ^ pretty_deep_term_helper body abs_prec)
  | App {head; arg; _} -> Utils.surround_prec app_prec prec (pretty_deep_term_helper head app_prec ^ " " ^ pretty_deep_term_helper arg (app_prec + 1))

and pretty_deep_term t = pretty_deep_term_helper t 0

let rec pretty_context_helper t pos prec =
  if t == pos
  then "<" ^ pretty_term t ^ ">"
  else match t with
    | Var { vref; _ } -> Utils.surround_prec var_prec prec vref.name
  | Abs {vref; body; _} -> Utils.surround_prec abs_prec prec ("λ" ^ vref.name ^ ". " ^ pretty_context_helper body pos abs_prec)
  | App {head; arg; _} -> Utils.surround_prec app_prec prec (pretty_context_helper head pos app_prec ^ " " ^ pretty_context_helper arg pos (app_prec + 1))

and pretty_context t pos = pretty_context_helper t pos 0


let rec extract_environment_helper acc t = match t with
  | Var v -> (match v.vref.sub with
               | NoSub -> acc
               | SubTerm t | SubValue t ->
                  (let entry = (v.vref.name, v.vref.sub, v.vref) in
                   (* Remove this substitution, to avoid duplicates. We shall restore it later *)
                   v.vref.sub <- NoSub;
                   entry :: extract_environment_helper acc t)
               | Copy _ -> raise InvalidTerm)
  | Abs a -> extract_environment_helper acc a.body
  | App a -> extract_environment_helper (extract_environment_helper acc a.head) a.arg

and extract_environment t =
  let env = extract_environment_helper [] t in
  (* Now, we restore all vrefs' substitutions to their old value and just return the pair name, sub*)
  List.map (fun (name, sub, vref) -> vref.sub <- sub; (name, sub)) env


let pretty_term_parent pc = match term_parent pc with
  | None -> ""
  | Some t -> pretty_term t

let rec get_term_root t = match term_parent t with
  | None -> t
  | Some p -> get_term_root p

let pretty_sub name sub = match sub with
  | NoSub -> ""
  | SubTerm t -> "[" ^ name ^ " <-- " ^ pretty_term t ^ "]"
  | SubValue t -> "[" ^ name ^ " <-- " ^ pretty_term t ^ " / value" ^ "]"
  | Copy _ -> raise InvalidTerm

let rec pretty_env env = match env with
  | [] -> ""
  | (name, sub) :: vrefs -> pretty_sub name sub ^ pretty_env vrefs
  

let pretty_chain c =
    let pretty_chain_helper t = Printf.sprintf "\t\tTerm: %s" (pretty_context (get_term_root t) t) in
    String.concat "\n" (List.map pretty_chain_helper c)

let print_state logger { pc; chain = chain; eval_done; betas } =
  Logger.log logger Logger.EvalTrace (lazy (
      let root = get_term_root pc in
      let env = extract_environment root in
      Printf.sprintf "Current state:\n\tEval done: %b\n\tBetas: %d\n\tTerm: %s\n\tEnv: %s\n\tChain: \n%s" eval_done betas (pretty_context root pc) (pretty_env env) (pretty_chain chain)
  ))

let rec eval logger s =
  if s.eval_done
  then s.pc
  else (step s; print_state logger s; eval logger s)

let run logger t =
  let s = { pc = t; chain = []; eval_done = false; betas = 0 } in
  print_state logger s;
  let res = eval logger s in
  Logger.log logger Logger.Summary (lazy (Printf.sprintf "Number of betas: %d\n" s.betas));
  res
