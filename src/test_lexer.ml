open Toyc_lib

let string_of_token = function
  | Toyc_parser.INT_TYPE -> "INT_TYPE"
  | Toyc_parser.VOID_TYPE -> "VOID_TYPE"
  | Toyc_parser.IF -> "IF"
  | Toyc_parser.ELSE -> "ELSE"
  | Toyc_parser.WHILE -> "WHILE"
  | Toyc_parser.BREAK -> "BREAK"
  | Toyc_parser.CONTINUE -> "CONTINUE"
  | Toyc_parser.RETURN -> "RETURN"
  | Toyc_parser.ID id -> "ID(" ^ id ^ ")"
  | Toyc_parser.NUMBER n -> "NUMBER(" ^ string_of_int n ^ ")"
  | Toyc_parser.ASSIGN -> "ASSIGN"
  | Toyc_parser.SEMICOLON -> "SEMICOLON"
  | Toyc_parser.LBRACE -> "LBRACE"
  | Toyc_parser.RBRACE -> "RBRACE"
  | Toyc_parser.LPAREN -> "LPAREN"
  | Toyc_parser.RPAREN -> "RPAREN"
  | Toyc_parser.OR -> "OR"
  | Toyc_parser.AND -> "AND"
  | Toyc_parser.LT -> "LT"
  | Toyc_parser.GT -> "GT"
  | Toyc_parser.LE -> "LE"
  | Toyc_parser.GE -> "GE"
  | Toyc_parser.EQ -> "EQ"
  | Toyc_parser.NE -> "NE"
  | Toyc_parser.PLUS -> "PLUS"
  | Toyc_parser.MINUS -> "MINUS"
  | Toyc_parser.MUL -> "MUL"
  | Toyc_parser.DIV -> "DIV"
  | Toyc_parser.MOD -> "MOD"
  | Toyc_parser.NOT -> "NOT"
  | Toyc_parser.EOF -> "EOF"
  | Toyc_parser.COMMA -> "COMMA"

let test_lexer source =
  let lexbuf = Lexing.from_string source in
  let rec loop () =
    let token = Toyc_lexer.token lexbuf in
    Printf.printf "%s\n" (string_of_token token);
    if token <> Toyc_parser.EOF then loop ()
  in
  loop ()

let () =
  let source = "int main() { return 42; }" in
  test_lexer source