(* Parser type  *)
type parser_context = { line: int; col: int; pos: int; input: string }
and 'a parse_result =
  | Success of 'a * parser_context
  | Failure of string * parser_context
and 'a parser = parser_context -> 'a parse_result

(* Some helpful parser combinators *)

(* Functor operations *)
let (<$>) f p =
  (fun ctx -> match p ctx with
                | Success (v, ctx2) -> Success (f v, ctx2)
                | Failure _ as fail -> fail)

let pure (v: 'a): 'a parser = (fun ctx -> Success (v, ctx))

(* Monad operations *)
let (>>=) p1 p2 =
  (fun ctx -> match p1 ctx with
                | Success (v, ctx2) -> p2 v ctx2
                | Failure _ as fail -> fail)

let ( let* ) = ( >>= )

(* Alternative operations: first try parser on the left, if it fails,
backtrack and then try parser on the right *)
let (<|>) (p1: 'a parser) (p2: 'a parser): 'a parser =
  (fun ctx -> match p1 ctx with
                | Failure _ -> p2 ctx
                | (Success _) as res -> res)

(* Sequencing *)
let ( *> ) (p1: 'a parser) (p2: 'b parser) =
  p1 >>= (fun _ -> p2)

let ( <* ) (p1: 'a parser) (p2: 'b parser) =
  let* v = p1 in
  let* _ = p2 in
  pure v


(* Fail *)
let parse_error (s: string) = (fun ctx -> Failure (s, ctx))

(* Apply parser p as long as there is not a failure *)
let parse_many p =
    (* Helper to make parse_many tail recursive *)
    let rec parse_many_helper acc p ctx = match p ctx with
                 | Success (v, ctx2) -> parse_many_helper (v :: acc) p ctx2
                 | Failure _ -> Success (acc, ctx)
    in List.rev <$> (parse_many_helper [] p)

(* Variant of parse_maby requiring p to succeed at least once *)
let parse_some p =
  let* r1 = p in
  let* rs = parse_many p in
  pure (r1 :: rs)

(* Recursion *)
let fix f =
  let rec r ctx = f r ctx
  in r

(* Parsing primitives *)

(* Read current char being processed, returns a `char option` which is None if the input is over *)
let peek_char ctx =
   if ctx.pos < String.length ctx.input
   then Success (Some (String.get ctx.input ctx.pos), ctx)
   else Success (None, ctx)

(* Move cursor *)
let consume_char ctx = 
   let update_ctx ctx =
        (* we assume a valid ctx, i.e. ctx.pos < String.length ctx.input *)
        if String.get ctx.input ctx.pos = '\n'
        then { line = ctx.line + 1; col = 1; pos = ctx.pos + 1; input = ctx.input }
        else { line = ctx.line; col = ctx.col + 1; pos = ctx.pos + 1; input = ctx.input }
   in
   if ctx.pos < String.length ctx.input
   then Success ((), update_ctx ctx)
   else Success ((), ctx) (* Consuming a char at end of input is a NOP *)

(* Expect char *)
let char c =
  let* v = peek_char in
  match v with
      | Some v when v = c -> (consume_char *> pure c)
      | None -> parse_error (Printf.sprintf "Unexpected end of file, expected char `%c`." c)
      | Some v -> parse_error (Printf.sprintf "Unexpected char `%c`, expected `%c`." v c)

(* Satisfy a predicate, fails if end of input is found *)
let satisfy pred =
  let* v = peek_char in
  match v with
      | Some v -> (if pred v then (consume_char *> pure v) else parse_error (Printf.sprintf "Unexpected char `%c`" v))
      | None -> parse_error (Printf.sprintf "Unexpected end of file.")

let not_char c = satisfy (fun v -> v != c)

(* Expect end of file *)
let expect_eof =
  let* v = peek_char in
  match v with
      | None -> pure ()
      | Some v -> parse_error (Printf.sprintf "Unexpected char `%c`, expected end of file." v)



(* Run a parser and return a Result*)
let run_parser p input = 
   let ctx = { line = 1; col = 1; pos = 0; input = input } in
   let make_parse_error msg ctx = (Printf.sprintf "Error at line %d, col %d: %s" ctx.line ctx.col msg) in
   match p ctx with
     | Success (v, _) -> Ok v
     | Failure (msg, ctx) -> Error (make_parse_error msg ctx)
  

(* Skip whitespaces *)
let skip_whitespaces = parse_many (satisfy (fun c -> String.contains " \n\r\t" c)) *> pure ()

(* parse one line comments, they start with # *)
let parse_one_line_comments = 
  let* _ = skip_whitespaces in
  let* _ = char '#' in
  parse_many (not_char '\n')

(* Skip whitespaces and comments *)
let ignoring_surroundings p = (parse_one_line_comments *> skip_whitespaces *> p) <|> (skip_whitespaces *> p)

(* Lexer utilities *)
let lexeme p = ignoring_surroundings p
let lexeme_char c = ignoring_surroundings (char c)

(* We provide a special combinator for parsing unicode codepoints
that expects the input to be encoded in UTF-8.
*)
let unicode_char uc = 
   let rec helper counter uc =
       if counter < String.length uc
       then (char (String.get uc counter) <|> parse_error (Printf.sprintf "Expected codepoint `%s`." uc)) *> helper (counter + 1) uc
       else pure ()
  in helper 0 uc *> pure uc
let lexeme_unicode_char uc = ignoring_surroundings (unicode_char uc)


(* Variable names are made of a single letter [a-zA-Z] *)
let parse_var_name = 
   let is_var_init c = (('A' <= c && c <= 'Z' ) || ('a' <= c && c <= 'z')) in
   let is_var_cont _ = false in
   let make_var_name list = 
      let buf = Buffer.create 16 in
      List.iter (Buffer.add_char buf) list;
      Buffer.contents buf
   in
   let* var_start = satisfy is_var_init in
   let* var_cont = parse_many (satisfy is_var_cont) in
   pure (make_var_name (var_start :: var_cont))

(* Lambda term parser *)
let parse_var =
   let* name = lexeme parse_var_name in
   pure (Syntax_tree.Var name)

let parse_term = fix (fun parse_term ->
  let parse_lambda =
       let* var = lexeme_char '\\' *> lexeme parse_var_name <* lexeme_char '.' in
       let* body = parse_term in
       pure (Syntax_tree.Abs (var, body))
  in let parse_fancy_lambda =
       let* var = lexeme_unicode_char "λ" *> lexeme parse_var_name <* lexeme_char '.' in
       let* body = parse_term in
       pure (Syntax_tree.Abs (var, body))
  in let parse_paren_term = lexeme_char '(' *> parse_term <* lexeme_char ')'
  in let parse_term1 = parse_lambda <|> parse_fancy_lambda <|> parse_var <|> parse_paren_term
  in let* ts = parse_some (lexeme parse_term1)
  in pure (List.fold_left (fun acc v -> Syntax_tree.App (acc, v)) (List.hd ts) (List.tl ts)))

let parse_program = parse_term <* (skip_whitespaces <* expect_eof)
