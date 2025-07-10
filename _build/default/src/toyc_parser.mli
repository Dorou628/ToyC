
(* The type of tokens. *)

type token = 
  | WHILE
  | VOID_TYPE
  | SEMICOLON
  | RPAREN
  | RETURN
  | RBRACE
  | PLUS
  | OR
  | NUMBER of (int)
  | NOT
  | NE
  | MUL
  | MOD
  | MINUS
  | LT
  | LPAREN
  | LE
  | LBRACE
  | INT_TYPE
  | IF
  | ID of (string)
  | GT
  | GE
  | EQ
  | EOF
  | ELSE
  | DIV
  | CONTINUE
  | COMMA
  | BREAK
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Toyc_ast.program)
