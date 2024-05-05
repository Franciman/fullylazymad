(* We assume that the input is a natural number in the range [0, 9] *)
let render_digit = function
  | 0 -> "₀"
  | 1 -> "₁"
  | 2 -> "₂"
  | 3 -> "₃"
  | 4 -> "₄"
  | 5 -> "₅"
  | 6 -> "₆"
  | 7 -> "₇"
  | 8 -> "₈"
  | 9 -> "₉"
  | _ -> "" (* impossible case *)

let rec render_subscript n = match n with
  | 0 -> ""
  | n -> render_subscript (n / 10) ^ render_digit (n mod 10)

let gen_fresh_name : string -> string =
  let counter = ref 0 in
  fun s -> counter := (!counter + 1); Printf.sprintf "%s%s" s (render_subscript !counter)


let surround_prec curr_prec ctx_prec s =
  if curr_prec < ctx_prec
  then "(" ^ s ^ ")"
  else s
