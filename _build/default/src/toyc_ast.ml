(* 二元运算符 *)
type binary_op =
  | Add | Sub | Mul | Div | Mod  (* 算术运算 *)
  | Lt | Gt | Le | Ge | Eq | Ne  (* 比较运算 *)
  | And | Or                     (* 逻辑运算 *)

(* 一元运算符 *)
type unary_op =
  | Not  (* 逻辑非 *)
  | Neg  (* 负号 *)
  | Pos  (* 正号 *)

(* 表达式 *)
type expr =
  | Id of string                      (* 标识符 *)
  | Num of int                        (* 数字常量 *)
  | Binary of binary_op * expr * expr  (* 二元运算 *)
  | Unary of unary_op * expr          (* 一元运算 *)
  | Call of string * expr list        (* 函数调用 *)
  | Assign of string * expr           (* 赋值 *)

(* 语句 *)
type stmt =
  | Block of stmt list                (* 语句块 *)
  | Expr of expr                      (* 表达式语句 *)
  | If of expr * stmt * stmt option   (* if-else语句 *)
  | While of expr * stmt              (* while循环 *)
  | Break                            (* break语句 *)
  | Continue                         (* continue语句 *)
  | Return of expr option            (* return语句 *)
  | Var_decl of string * expr        (* 变量声明 *)

(* 函数参数 *)
type param = {
  name: string;                      (* 参数名 *)
}

(* 函数定义 *)
type function_def = {
  name: string;                      (* 函数名 *)
  params: param list;                (* 参数列表 *)
  return_type: bool;                 (* 返回类型：true表示int，false表示void *)
  body: stmt list;                   (* 函数体 *)
}

(* 程序结构 *)
type program = {
  functions: function_def list;      (* 函数定义列表 *)
}