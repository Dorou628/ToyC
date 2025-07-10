open Toyc_lib.Toyc_ast

(* 测试函数：解析源代码并打印AST *)
let test_parse filename =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  try
    let ast = Toyc_lib.Toyc_parser.program Toyc_lib.Toyc_lexer.token lexbuf in
    close_in ic;
    ast
  with
    | Toyc_lib.Toyc_parser.Error ->
        Printf.printf "语法错误\n";
        close_in ic;
        exit 1
    | Failure msg ->
        Printf.printf "解析失败：%s\n" msg;
        close_in ic;
        exit 1

(* 打印二元运算符 *)
let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Lt -> "<" | Gt -> ">" | Le -> "<=" | Ge -> ">=" | Eq -> "==" | Ne -> "!="
  | And -> "&&" | Or -> "||"

(* 打印一元运算符 *)
let string_of_unop = function
  | Not -> "!" | Neg -> "-" | Pos -> "+"

(* 打印表达式 *)
let rec string_of_expr = function
  | Id name -> name
  | Num n -> string_of_int n
  | Binary (op, e1, e2) ->
      "(" ^ string_of_expr e1 ^ " " ^ string_of_binop op ^ " " ^ string_of_expr e2 ^ ")"
  | Unary (op, e) ->
      "(" ^ string_of_unop op ^ string_of_expr e ^ ")"
  | Call (name, args) ->
      name ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | Assign (name, e) ->
      name ^ " = " ^ string_of_expr e

(* 打印语句 *)
let rec string_of_stmt indent = function
  | Block stmts ->
      let indent_str = String.make indent ' ' in
      "\n" ^ indent_str ^ "{"
      ^ String.concat "" (List.map (string_of_stmt (indent + 2)) stmts)
      ^ "\n" ^ indent_str ^ "}"
  | Expr e -> "\n" ^ String.make indent ' ' ^ string_of_expr e ^ ";"
  | If (cond, then_stmt, else_stmt) ->
      let indent_str = String.make indent ' ' in
      "\n" ^ indent_str ^ "if (" ^ string_of_expr cond ^ ")"
      ^ string_of_stmt indent then_stmt
      ^ (match else_stmt with
         | Some stmt -> "\n" ^ indent_str ^ "else" ^ string_of_stmt indent stmt
         | None -> "")
  | While (cond, body) ->
      let indent_str = String.make indent ' ' in
      "\n" ^ indent_str ^ "while (" ^ string_of_expr cond ^ ")"
      ^ string_of_stmt indent body
  | Break -> "\n" ^ String.make indent ' ' ^ "break;"
  | Continue -> "\n" ^ String.make indent ' ' ^ "continue;"
  | Return None -> "\n" ^ String.make indent ' ' ^ "return;"
  | Return (Some e) -> "\n" ^ String.make indent ' ' ^ "return " ^ string_of_expr e ^ ";"
  | Var_decl (name, init) ->
      "\n" ^ String.make indent ' ' ^ "int " ^ name ^ " = " ^ string_of_expr init ^ ";"

(* 打印函数参数 *)
let string_of_param (param : Toyc_lib.Toyc_ast.param) =
  "int " ^ param.name

(* 打印函数定义 *)
let string_of_function (f : Toyc_lib.Toyc_ast.function_def) =
  (if f.return_type then "int" else "void") ^ " " ^ f.name
  ^ "(" ^ String.concat ", " (List.map string_of_param f.params) ^ ")"
  ^ " {\n" ^ String.concat "" (List.map (string_of_stmt 2) f.body) ^ "}"

(* 打印程序 *)
let string_of_program prog =
  String.concat "\n\n" (List.map string_of_function prog.functions)

(* 主函数：解析并打印AST *)
let () =
  if Array.length Sys.argv < 2 then
    Printf.printf "用法: %s <源文件>\n" Sys.argv.(0)
  else
    let ast = test_parse Sys.argv.(1) in
    print_endline (string_of_program ast)