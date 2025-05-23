type term =
  | Var of { v: var_ref; mutable taken: bool; mutable parent: term option }
  | Abs of { v: var_ref; mutable body: term; mutable occurrences: term list; mutable taken: bool; mutable parent: term option }
  | App of { mutable head: term; mutable arg: term; mutable taken: bool; mutable parent: term option }

(* We also store the original name to be used as basis for generating fresh names *)
and var_ref =
 { mutable prev : var_ref option;
   orig_name : string;
   name : string;
   mutable refno : int; (* only meaningful when there is a substitution *)
   mutable sub : sub;
   mutable next : var_ref option }
and sub =
    NoSub
  | Sub of term
  | SubSkel of term
  | Hole
  | Copy of (term list ref * var_ref)

type env = var_ref option

(* Operations on the environment *)
let push vref env =
 vref.next <- env ;
 Option.iter (fun v -> v.prev <- Some vref) env

let split vref =
 let env' = vref.next in
 vref.next <- None ;
 Option.iter (fun v -> v.prev <- None) env' ;
 env'

exception UnboundVariable of string
exception BoundedTwice of string
exception InvalidTerm

let make_fresh_var (orig_name: string) = 
  let name = if orig_name = "dummy" then "dummy" else Utils.gen_fresh_name orig_name in
  { prev = None; orig_name = orig_name; name; sub = NoSub; refno = 0; next = None }

  
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
let rec extract_flesh env mt = match mt with
  | Var v -> v.taken <- false ; mt
  | Abs { taken = false; _}
  | App { taken = false; _} ->
     let fresh_vref = make_fresh_var "p" in
     fresh_vref.refno <- 1;
     let p = get_parent mt in
     set_parent mt None;
     fresh_vref.sub <- Sub mt;
     push fresh_vref !env;
     env := Some fresh_vref;
     Var { v=fresh_vref ; taken=false ; parent = p }
  | Abs a ->
     a.taken <- false;
     a.body <- extract_flesh env a.body;
     mt
  | App a ->
     a.taken <- false;
     a.head <- extract_flesh env a.head;
     a.arg <- extract_flesh env a.arg;
     mt

let extract_skeleton env t = match t with
  | Abs _ ->
     mark_skeleton (Some t);
     let env = ref env in
     let res = extract_flesh env t in
     res,!env
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
          let vref = { prev = None; orig_name = v; name = v; refno = 0; sub = NoSub; next = None } in
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
     v.refno <- v.refno + 1;
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
and chain = (var_ref * stack * env) list (* v.prev (back)points to the (tail of the) env *)
and roots = var_ref list
and state = chain * term * stack * env * roots

(* Pretty printer *)

let var_prec = 3
let app_prec = 2
let abs_prec = 1

let rec pretty_term_helper t prec = match t with
  | Var {v={ name = name; _ }; _} -> Utils.surround_prec var_prec prec name
  | Abs {v; body; _} -> Utils.surround_prec abs_prec prec ("λ" ^ v.name ^ "." ^ pretty_term_helper body abs_prec)
  | App {head; arg; _} -> Utils.surround_prec app_prec prec (pretty_term_helper head app_prec ^ "" ^ pretty_term_helper arg (app_prec + 1))

and pretty_term t = pretty_term_helper t 0

let pretty_stack s = String.concat ":" (List.map (fun t -> pretty_term_helper t app_prec) s)

let pretty_sub name sub = match sub with
  | NoSub -> ""
  | Sub t -> "[" ^ name ^ "←" ^ pretty_term t ^ "]"
  | SubSkel t -> "<" ^ name ^ "←" ^ pretty_term t ^ ">"
  | Hole -> "[" ^ name ^ "←.]"
  | Copy _ -> raise InvalidTerm

let rec pretty_env_helper env =
 match env with
 | None -> []
 | Some {name; sub; next; _} ->
    pretty_sub name sub :: pretty_env_helper next

let pretty_env env =
 String.concat ":" (pretty_env_helper env)
  
let pretty_chain c =
  let pretty_chain_helper (v, s, env) = 
   Printf.sprintf "(\027[4m%s\027[0;31m,%s,%s)" v.name (pretty_stack s) (pretty_env env) in
  String.concat ":" (List.rev_map pretty_chain_helper c)

let pretty_roots vars =
  String.concat ":" (List.map (fun {name; _} -> name) vars)

let print_state logger trans (c, t, s, env, roots) =
  Logger.log logger Logger.EvalTrace (lazy (
    Printf.sprintf "%s\t\027[31m%s\027[0m|\027[4m%s\027[0m|%s|\027[32m%s\027[0m|\027[35m%s\027[0m" trans (pretty_chain c) (pretty_term t) (pretty_stack s) (pretty_env env) (pretty_roots roots)
  ))

(* Garbage collection *)

let rec roots_of_term =
 function
  | Var { v; _ } ->
     if v.sub <> NoSub then begin
      v.refno <- v.refno - 1;
      if v.refno = 0 then
       [v]
      else
       []
     end else []
  | Abs { body; _ } -> roots_of_term body
  | App { head; arg; _ } -> roots_of_term head @ roots_of_term arg

let new_roots {sub; _} =
 (match sub with
  | Sub t
  | SubSkel t -> roots_of_term t
  | NoSub
  | Hole
  | Copy _ -> assert false)

let detach {prev; next; _} =
 Option.iter (fun v -> v.prev <- prev) next;
 Option.iter (fun v -> v.next <- next) prev

let with_env env f x =
 let fakevar = make_fresh_var "dummy" in
 push fakevar env;
 f x;
 fakevar.next

let step : state -> string * state =
 function
  | chain, App { head; arg; _ }, args, env, [] ->
      set_parent head None;
      set_parent arg None;
      "sea₁",(chain, head, arg :: args, env, [])
  | chain, Abs { v; body; occurrences=(_::_ as occurrences); _ }, arg :: args, env, [] ->
      set_parent body None;
      v.sub <- Sub arg;
      v.refno <- List.length occurrences;
      push v env;
      "β₁",(chain, body, args, Some v, [])
  | chain, Abs { v; body; occurrences=[]; _ }, arg :: args, env, [] ->
      set_parent body None;
      v.sub <- Sub arg;
      v.refno <- 0;
      push v env;
      "β₂",(chain, body, args, Some v, [v])
  | chain, Var ({v={sub=Sub (App _ | Var _ as t); _} as vref; _}), stack, env, [] ->
      vref.sub <- Hole;
      let env' = split vref in
      "sea₂",((vref, stack, env) :: chain, t, [], env', [])
  | (vref, stack, env)::chain, (Abs _ as value), [], env', [] ->
      vref.sub <- Sub value;
      push vref env';
      "sea₃",(chain, Var {v=vref; taken=false; parent=None}, stack, env, [])
  | _chain, Var ({v={sub=Sub (Abs _ as v); _} as vref; _}), _stack, _env, [] as s ->
      let skel,env'' = extract_skeleton vref.next v in
      vref.sub <- SubSkel skel;
      push vref env'';
      "sk",s
  | chain, Var ({v={sub=SubSkel v; refno; _} as vref; _}), stack, env, [] when refno <> 1 ->
      vref.refno <- refno - 1;
      "ss₁",(chain, rename_term v, stack, env, [])
  | chain, Var ({v={sub=SubSkel v; _} as vref; _}), stack, env, [] ->
      let env = with_env env detach vref in
      "ss₂",(chain, v, stack, env, [])
  | chain, t, stack, env, x::roots ->
      let roots' = new_roots x in
      let env = with_env env detach x in
      "gc",(chain,t,stack,env,roots'@roots)
  | [], Abs _, [], _env, [] ->
     assert false (* stepping over a normal term *)
  | _chain, Var {v={sub=NoSub; name; _}; _}, _stack, _env, _roots ->
     raise (UnboundVariable name)
  | _chain, Var {v={sub=(Copy _ | Hole); _}; _}, _stack, _env, _roots ->
     raise InvalidTerm

let rec eval logger betas =
 function
   | ([], (Abs _ as value), [], _env, []) ->
      (* Normal form reached *)
      Logger.log logger Logger.Summary (lazy (Printf.sprintf "Number of betas: %d\n" betas));
      value
  | state ->
     let trans,next_state = step state in
     print_state logger ("→"^trans) next_state;
     eval logger (if trans="β₁" || trans="β₂" then betas+1 else betas) next_state

let run logger t =
  let s = ([], t, [], None, []) in
  print_state logger "" s;
  eval logger 0 s
