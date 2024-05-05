{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let id = (alpha) (alpha|digit|'_')*
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read_token = parse
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '\\' { LAMBDA }
  | "λ" { LAMBDA }
  | '.' { DOT }
  | whitespace { read_token lexbuf }
  | "//" { read_single_line_comment lexbuf }
  | "(*" { read_multi_line_comment lexbuf }
  | id { ID (Lexing.lexeme lexbuf) }
  | newline { next_line lexbuf; read_token lexbuf }
  | eof { EOF }
  | _ { raise (SyntaxError ("Lexer - Illegal character: " ^ Lexing.lexeme lexbuf)) }

and read_single_line_comment = parse
  | newline { next_line lexbuf; read_token lexbuf }
  | eof { EOF }
  | _ { read_single_line_comment lexbuf }

and read_multi_line_comment = parse
  | "*)" { read_token lexbuf }
  | newline { next_line lexbuf; read_multi_line_comment lexbuf }
  | eof { raise (SyntaxError ("Lexer - Unexpected EOF - unterminating comment")) }
  | _ { read_multi_line_comment lexbuf }
