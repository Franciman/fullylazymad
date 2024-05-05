type term =
    Var of string
  | Abs of string * term
  | App of term * term

let var_prec = 3
let app_prec = 2
let abs_prec = 1


let rec print_syntax_tree_helper (t: term) prec = match t with
  | Var v -> Utils.surround_prec var_prec prec v
  | Abs (v, t) -> Utils.surround_prec abs_prec prec ("λ" ^ v ^ ". " ^ print_syntax_tree_helper t abs_prec)
  | App (head, arg) -> Utils.surround_prec app_prec prec (print_syntax_tree_helper head app_prec ^ " " ^ print_syntax_tree_helper arg (app_prec + 1))

let print_syntax_tree t = print_syntax_tree_helper t 0
