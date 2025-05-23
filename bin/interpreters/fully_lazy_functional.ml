type term =
  | Var of { v: var_ref; mutable taken: bool; mutable parent: term option }
  | Abs of { v: var_ref; mutable body: term; mutable occurrences: term list; mutable taken: bool; mutable parent: term option }
  | App of { mutable head: term; mutable arg: term; mutable taken: bool; mutable parent: term option }

(* We also store the original name to be used as basis for generating fresh names *)
and var_ref = { orig_name : string; name : string; mutable sub : sub }
and sub =
    NoSub
  | Sub of term
  | SubSkel of term
  | Hole
  | Copy of (term list ref * var_ref)

exception UnboundVariable of string
exception BoundedTwice of string
exception InvalidTerm

let make_fresh_var (orig_name: string) = 
  { orig_name = orig_name; name = Utils.gen_fresh_name orig_name; sub = NoSub }

  
(* Skeleton extraction *)
let get_parent mt = match mt with
  | Var v -> v.parent
  | Abs a -> a.parent
  | App a -> a.parent

let set_parent mt p = match mt with
  | Var v -> v.parent <- p
  | Abs a -> a.parent <- p
  | App a -> a.parent <- p
  
let rec mark_skeleton =
 function
  | None -> ()
  | Some (Var v) -> (v.taken <- true; mark_skeleton v.parent)
  | Some (Abs a) ->
      if not a.taken
      then (a.taken <- true;
            List.iter (fun v -> mark_skeleton (Some v)) a.occurrences;
            mark_skeleton a.parent)
  | Some (App a) ->
      if not a.taken
      then (a.taken <- true; mark_skeleton a.parent)
      
(* Extract flesh and unmark the skeleton *)
let rec extract_flesh mt = match mt with
  | Var v -> v.taken <- false ; mt
  | Abs { taken = false; _}
  | App { taken = false; _} ->
     let fresh_vref = make_fresh_var "p" in
     let p = get_parent mt in
     set_parent mt None;
     fresh_vref.sub <- Sub mt;
     Var { v=fresh_vref ; taken=false ; parent = p }
  | Abs a ->
     a.taken <- false;
     a.body <- extract_flesh a.body;
     mt
  | App a ->
     a.taken <- false;
     a.head <- extract_flesh a.head;
     a.arg <- extract_flesh a.arg;
     mt

let extract_skeleton t = match t with
  | Abs _ ->
     mark_skeleton (Some t);
     extract_flesh t
  | Var _ | App _ -> raise InvalidTerm

(* Convert a Syntax_tree.term in a term *)

let rec scope_checker env avoid (t: Syntax_tree.term): string list * term =
  match t with
    | Var v ->
       (match List.assoc_opt v env with
         | Some (occ,vref) ->
             let res = Var {v=vref; taken=false; parent=None} in
             occ := res::!occ;
             avoid,res
         | None -> raise (UnboundVariable v))
    | Abs (v, body) ->
       (if List.mem v avoid then
         raise (BoundedTwice v)
        else
         let vref = { orig_name = v; name = v; sub = NoSub } in
         let occ = ref [] in
         let avoid,body = scope_checker ((v, (occ, vref)) :: env) (v::avoid) body in
         let res = Abs { v = vref; body; taken=false; parent=None; occurrences= !occ } in
         set_parent body (Some res);
         avoid, res)
    | App (head, arg) ->
        let avoid,head = scope_checker env avoid head in
        let avoid,arg = scope_checker env avoid arg in
        let res = App { head ; arg ; taken=false; parent=None } in
        set_parent head (Some res);
        set_parent arg (Some res);
        avoid, res

let scope_check t = snd (scope_checker [] [] t)

(* Interpreter *)

let rec rename_term (t: term) = match t with
  | Var {v={sub = Copy (occ,v); _}; _} ->
     let res = Var {v; taken=false; parent=None} in
     occ := res::!occ;
     res
  | Var {v; _} ->
     Var {v; taken=false; parent=None}
  | Abs { v; body; _ } ->
      let fresh_v = make_fresh_var v.orig_name in
      let occ = ref [] in
      v.sub <- Copy (occ, fresh_v);
      let body' = rename_term body in
      v.sub <- NoSub;
      let res = Abs { v = fresh_v; body = body' ; taken=false; parent=None; occurrences = !occ} in
      set_parent body' (Some res);
      res
  | App { head; arg; _ } -> 
      let head' = rename_term head in
      let arg' = rename_term arg in
      let res = App { head = head'; arg = arg'; taken=false; parent=None } in
      set_parent head' (Some res);
      set_parent arg' (Some res);
      res
      
type stack = term list
and chain = (var_ref * stack) list 
and state = chain * term * stack

(* Pretty printer *)

let var_prec = 3
let app_prec = 2
let abs_prec = 1

let rec pretty_term_helper t prec = match t with
  | Var {v={ name = name; _ }; _} -> Utils.surround_prec var_prec prec name
  | Abs {v; body; _} -> Utils.surround_prec abs_prec prec ("λ" ^ v.name ^ "." ^ pretty_term_helper body abs_prec)
  | App {head; arg; _} -> Utils.surround_prec app_prec prec (pretty_term_helper head app_prec ^ "" ^ pretty_term_helper arg (app_prec + 1))

and pretty_term t = pretty_term_helper t 0

let extract_environment ~avoid s =
 let rec extract_environment_helper acc t = match t with
  | Var {v;_} -> (match v.sub with
               | _ when List.exists (fun (_,_,v') -> v==v') avoid -> acc
               | NoSub -> acc
               | Sub t | SubSkel t ->
                  let entry = (v.name, v.sub, v) in
                  extract_environment_helper (entry::(List.filter (fun (_,_,v') -> v!=v') acc)) t
               | Hole -> (v.name, v.sub, v)::acc
               | Copy _ -> raise InvalidTerm)
  | Abs a -> extract_environment_helper acc a.body
  | App a -> extract_environment_helper (extract_environment_helper acc a.head) a.arg
 in
  List.rev (List.fold_left (extract_environment_helper) [] s)


let pretty_stack s = String.concat ":" (List.map (fun t -> pretty_term_helper t app_prec) s)

let pretty_sub name sub = match sub with
  | NoSub -> ""
  | Sub t -> "[" ^ name ^ "←" ^ pretty_term t ^ "]"
  | SubSkel t -> "<" ^ name ^ "←" ^ pretty_term t ^ ">"
  | Hole -> "[" ^ name ^ "←.]"
  | Copy _ -> raise InvalidTerm

let pretty_env env = String.concat ":" (List.map (fun (name,sub,_) -> pretty_sub name sub) env)
  

let pretty_chain ~avoid c =
  let pretty_chain_helper ~avoid (v, s) = 
    let env = extract_environment ~avoid s in
    let avoid = (v.name,v.sub,v)::avoid in
    env@avoid,Printf.sprintf "(\027[4m%s\027[0;31m,%s,%s)"  v.name (pretty_stack s) (pretty_env env) in
  let _,l = List.fold_left (fun (avoid,l) ci -> let avoid,i = pretty_chain_helper ~avoid ci in avoid,i::l) (avoid,[]) c  in
  String.concat ":" l


let print_state logger trans (c, t, s) =
  Logger.log logger Logger.EvalTrace (lazy (
    let env = extract_environment ~avoid:[] (t::s) in
    Printf.sprintf "%s\t\027[31m%s\027[0m|\027[4m%s\027[0m|%s|\027[32m%s\027[0m" trans (pretty_chain ~avoid:env c) (pretty_term t) (pretty_stack s) (pretty_env env)
  ))


let step : state -> string * state =
 function
  | chain, App { head; arg; _ }, args ->
      set_parent head None;
      set_parent arg None;
      "sea₁ ",(chain, head, arg :: args)
  | chain, Abs { v; body; _ }, arg :: args ->
      set_parent body None;
      v.sub <- Sub arg;
      "β",(chain, body, args)
  | chain, Var ({v={sub=Sub (App _ | Var _ as t); _} as vref; _}), stack ->
      vref.sub <- Hole;
      "sea₂",((vref, stack) :: chain, t, [])
  | (vref, stack)::chain, (Abs _ as value), [] ->
      vref.sub <- Sub value;
      "sea₃",(chain, Var {v=vref; taken=false; parent=None}, stack)
  | _chain, Var ({v={sub=Sub (Abs _ as v); _} as vref; _}), _stack as s ->
      let skel = extract_skeleton v in
      vref.sub <- SubSkel skel;
      "sk",s
  | chain, Var ({v={sub=SubSkel v; _}; _}), stack ->
      "ss",(chain, rename_term v, stack)
  | [], Abs _, [] ->
     assert false (* stepping over a normal term *)
  | _chain, Var {v={sub=NoSub; name; _}; _}, _stack ->
     raise (UnboundVariable name)
  | _chain, Var {v={sub=(Copy _ | Hole); _}; _}, _stack ->
     raise InvalidTerm

let rec eval logger betas =
 function
   | ([], (Abs _ as value), []) ->
      (* Normal form reached *)
      Logger.log logger Logger.Summary (lazy (Printf.sprintf "Number of betas: %d\n" betas));
      value
  | state ->
     let trans,next_state = step state in
     print_state logger ("→"^trans) next_state;
     eval logger (if trans="β" then betas+1 else betas) next_state

let run logger t =
  let s = ([], t, []) in
  print_state logger "" s;
  eval logger 0 s
