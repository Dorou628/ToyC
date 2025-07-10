{
  open Toyc_parser (* 假设有一个对应的parser模块 *)
  
  exception Lexical_error of string
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = ['_' 'a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*

rule token = parse
  | '\239' '\187' '\191' { token lexbuf } (* 跳过UTF-8 BOM字符 *)
  | [' ' '\t' '\n' '\r'] { token lexbuf } (* 跳过空白字符 *)
  | "//" [^ '\n']* '\n' { token lexbuf } (* 单行注释 *)
  | "/*" { comment lexbuf; token lexbuf } (* 多行注释 *)
  
  (* 关键字 *)
  | "int" { INT_TYPE }
  | "void" { VOID_TYPE }
  | "if" { IF }
  | "else" { ELSE }
  | "while" { WHILE }
  | "break" { BREAK }
  | "continue" { CONTINUE }
  | "return" { RETURN }
  
  (* 标识符 *)
  | ident as id { ID id }
  
  (* 数字 *)
  | '-'? ('0' | ['1'-'9'] digit*) as num { 
      try NUMBER (int_of_string num) 
      with Failure _ -> raise (Lexical_error ("Invalid number: " ^ num))
    }
  
  (* 运算符 *)
  | "=" { ASSIGN }
  | ";" { SEMICOLON }
  | "," { COMMA }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "||" { OR }
  | "&&" { AND }
  | "<" { LT }
  | ">" { GT }
  | "<=" { LE }
  | ">=" { GE }
  | "==" { EQ }
  | "!=" { NE }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MUL }
  | "/" { DIV }
  | "%" { MOD }
  | "!" { NOT }
  
  | eof { EOF }
  
  | _ { raise (Lexical_error ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }

and comment = parse
  | "*/" { () }
  | "/*" { comment lexbuf; comment lexbuf }
  | _ { comment lexbuf }
  | eof { raise (Lexical_error "Unterminated comment") }
