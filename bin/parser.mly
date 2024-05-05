%{
open Syntax_tree
%}

%token LPAREN
%token RPAREN
%token LAMBDA
%token DOT
%token <string> ID
%token EOF

%start <syntax_tree> program

%nonassoc LPAREN
%left higher
%nonassoc LAMBDA

%%

program : t = term; EOF { t };

term :
  | name = ID { Var name }
  | LAMBDA; arg = ID; DOT; body = term { Abs (arg, body) }
  | head = term; arg = term %prec higher { App (head, arg) }
  | LPAREN; t = term; RPAREN { t }
