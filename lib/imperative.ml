type term =
    Var of { vref: var_ref; mutable parent: term option }
  | Abs of { vref: var_ref; body: term; mutable parent: term option }
  | App of { mutable head: term; arg: term; mutable parent: term option }
and var_ref = { orig_name: string; name: string; mutable sub: sub }
and sub =
    NoSub
  | SubTerm of term
  | SubValue of term
  | Copy of var_ref
and state = {
  mutable pc: term;
  (* Terms in the chain are only of type Var *)
  mutable chain: term list;
  mutable eval_done: bool
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

let add_to_chain o ts = match o with
  | None -> ts
  | Some t -> t :: ts

(* Convert a Syntax_tree.term in a term *)

let rec scope_checker env (t: Syntax_tree.term) (parent: term option): term =
   match t with
     | Var v -> (match List.assoc_opt v env with
                  | Some vref -> Var { vref; parent }
                  | None -> raise (UnboundVariable v))
    | Abs (v, body) ->
       let vref: var_ref = { orig_name = v; name = v; sub = NoSub } in
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


(* Pretty printer *)

let var_prec = 3
let app_prec = 2
let abs_prec = 1

let rec pretty_term_helper t prec = match t with
  | Var { vref; _ } -> (match vref.sub with
                         | NoSub -> Utils.surround_prec var_prec prec vref.name
                         | SubTerm t -> Utils.surround_prec var_prec prec (vref.name ^ "[" ^ vref.name ^ "<= " ^ pretty_term t ^ "]")
                         | SubValue t -> Utils.surround_prec var_prec prec (vref.name ^ "[" ^ vref.name ^ "<- " ^ pretty_term t ^ "]")
                         | Copy _ -> raise InvalidTerm)
  | Abs {vref; body; _} -> Utils.surround_prec abs_prec prec ("λ" ^ vref.name ^ ". " ^ pretty_term_helper body abs_prec)
  | App {head; arg; _} -> Utils.surround_prec app_prec prec (pretty_term_helper head app_prec ^ " " ^ pretty_term_helper arg (app_prec + 1))

and pretty_term t = pretty_term_helper t 0



let make_fresh_var (orig_name: string) = 
  { orig_name = orig_name; name = Utils.gen_fresh_name orig_name; sub = NoSub }

let rec rename_term = function
  | Var v as var -> 
      (match v.vref.sub with
         | Copy v_new -> Var { vref = v_new; parent = v.parent }
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

let rec pretty_chain = function
  | [] -> ""
  | (Var {vref; _}) :: cs -> vref.name ^ ", " ^ pretty_chain cs
  | _ -> raise InvalidTerm

let pretty_term_parent pc = match term_parent pc with
  | None -> ""
  | Some t -> pretty_term t

let print_state { pc; chain; eval_done } =
  Printf.printf "CURRENT STATE:\n\tTERM: %s\n\tTERM PARENT: %s\n\tCHAIN: %s\n\tEVAL DONE: %b\n" (pretty_term pc) (pretty_term_parent pc) (pretty_chain chain) eval_done

let rec eval s =
  if s.eval_done
  then s.pc 
  else (step s; print_state s; eval s)

let run t =
  let s = { pc = t; chain = []; eval_done = false } in
  print_state s;
  eval s
