(* RISC-V代码生成器 *)
open Toyc_ast

(* 寄存器分配 *)
type register = 
  | Zero  (* x0, 硬件零 *)
  | RA    (* x1, 返回地址 *)
  | SP    (* x2, 栈指针 *)
  | T0    (* x5, 临时寄存器 *)
  | T1    (* x6, 临时寄存器 *)
  | A0    (* x10, 参数/返回值 *)

(* 指令类型 *)
type instruction =
  | Li of register * int       (* 加载立即数 *)
  | Add of register * register * register  (* 加法 *)
  | Sub of register * register * register  (* 减法 *)
  | Mul of register * register * register  (* 乘法 *)
  | Div of register * register * register  (* 除法 *)
  | Rem of register * register * register  (* 取余 *)
  | Sw of register * register * int       (* 存储字 *)
  | Lw of register * register * int       (* 加载字 *)
  | J of string                (* 无条件跳转 *)
  | Beq of register * register * string   (* 相等跳转 *)
  | Bne of register * register * string   (* 不等跳转 *)
  | Blt of register * register * string   (* 小于跳转 *)
  | Bge of register * register * string   (* 大于等于跳转 *)
  | Ble of register * register * string   (* 小于等于跳转 *)
  | Bgt of register * register * string   (* 大于跳转 *)
  | Label of string            (* 标签 *)
  | Comment of string          (* 注释 *)
  | Slt of register * register * register (* 小于设置 *)
  | Seqz of register * register          (* 等于零设置 *)
  | Snez of register * register          (* 不等于零设置 *)
  | And of register * register * register (* 与运算 *)
  | Or of register * register * register  (* 或运算 *)
  | Jal of string              (* 跳转并链接 *)
  | Jr of register             (* 跳转到寄存器 *)

(* 将寄存器转换为字符串 *)
let string_of_register = function
  | Zero -> "zero"
  | RA -> "ra"
  | SP -> "sp"
  | T0 -> "t0"
  | T1 -> "t1"
  | A0 -> "a0"

(* 将指令转换为RISC-V汇编字符串 *)
let string_of_instruction = function
  | Li (rd, imm) -> Printf.sprintf "\tli %s, %d" (string_of_register rd) imm
  | Add (rd, rs1, rs2) -> Printf.sprintf "\tadd %s, %s, %s" 
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Sub (rd, rs1, rs2) -> Printf.sprintf "\tsub %s, %s, %s"
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Mul (rd, rs1, rs2) -> Printf.sprintf "\tmul %s, %s, %s"
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Div (rd, rs1, rs2) -> Printf.sprintf "\tdiv %s, %s, %s"
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Rem (rd, rs1, rs2) -> Printf.sprintf "\trem %s, %s, %s"
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Sw (rs, base, offset) -> Printf.sprintf "\tsw %s, %d(%s)"
      (string_of_register rs) offset (string_of_register base)
  | Lw (rd, base, offset) -> Printf.sprintf "\tlw %s, %d(%s)"
      (string_of_register rd) offset (string_of_register base)
  | J label -> Printf.sprintf "\tj %s" label
  | Beq (rs1, rs2, label) -> Printf.sprintf "\tbeq %s, %s, %s"
      (string_of_register rs1) (string_of_register rs2) label
  | Bne (rs1, rs2, label) -> Printf.sprintf "\tbne %s, %s, %s"
      (string_of_register rs1) (string_of_register rs2) label
  | Blt (rs1, rs2, label) -> Printf.sprintf "\tblt %s, %s, %s"
      (string_of_register rs1) (string_of_register rs2) label
  | Bge (rs1, rs2, label) -> Printf.sprintf "\tbge %s, %s, %s"
      (string_of_register rs1) (string_of_register rs2) label
  | Ble (rs1, rs2, label) -> Printf.sprintf "\tble %s, %s, %s"
      (string_of_register rs1) (string_of_register rs2) label
  | Bgt (rs1, rs2, label) -> Printf.sprintf "\tbgt %s, %s, %s"
      (string_of_register rs1) (string_of_register rs2) label
  | Label label -> Printf.sprintf "%s:" label
  | Comment text -> Printf.sprintf "\t# %s" text
  | Slt (rd, rs1, rs2) -> Printf.sprintf "\tslt %s, %s, %s"
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Seqz (rd, rs) -> Printf.sprintf "\tseqz %s, %s"
      (string_of_register rd) (string_of_register rs)
  | Snez (rd, rs) -> Printf.sprintf "\tsnez %s, %s"
      (string_of_register rd) (string_of_register rs)
  | And (rd, rs1, rs2) -> Printf.sprintf "\tand %s, %s, %s"
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Or (rd, rs1, rs2) -> Printf.sprintf "\tor %s, %s, %s"
      (string_of_register rd) (string_of_register rs1) (string_of_register rs2)
  | Jal label -> Printf.sprintf "\tjal %s" label
  | Jr reg -> Printf.sprintf "\tjr %s" (string_of_register reg)

(* 生成唯一的标签 *)
let label_counter = ref 0
let generate_label prefix =
  let label = Printf.sprintf "%s_%d" prefix !label_counter in
  incr label_counter;
  label

(* 代码生成上下文 *)
type var_info = {
  offset: int;
  var_type: bool; (* true for int, false for void *)
}

type context = {
  instructions: instruction list;
  variables: (string * var_info) list;
  next_offset: int;
  stack_size: int;
  current_function: string option;
}

(* 创建初始上下文 *)
let create_context () = {
  instructions = [];
  variables = [];
  next_offset = -8;  (* 从-8开始，因为-4是返回地址 *)
  stack_size = 24;   (* 固定栈帧大小：返回地址(4) + 3个变量(12) + 临时变量(8) *)
  current_function = None;
}

(* 创建新的上下文 *)
let new_context () = {
  instructions = [];
  stack_size = 0;
  current_function = None;
  variables = [];
  next_offset = -8; (* 从-8开始，因为-4是返回地址 *)
}

(* 添加指令到上下文 *)
let add_instruction context instr =
  { context with instructions = context.instructions @ [instr] }

(* 添加变量到上下文 *)
let add_variable context name var_type =
  let var_info = {
    offset = context.next_offset;
    var_type = var_type;
  } in
  { context with
    variables = (name, var_info) :: context.variables;
    next_offset = context.next_offset - 4;
    stack_size = context.stack_size + 4
  }

(* 查找变量信息 *)
let find_variable context name =
  try Some (List.assoc name context.variables)
  with Not_found -> None

(* 生成表达式代码 *)
let rec generate_expr context expr =
  match expr with
  | Num n ->
      let context = add_instruction context (Li (T0, n)) in
      context, T0
  | Id name ->
      (match find_variable context name with
      | Some var_info ->
          let context = add_instruction context (Lw (T0, SP, var_info.offset)) in
          context, T0
      | None -> failwith ("Undefined variable: " ^ name))
  | Binary (op, e1, e2) ->
      let context, r1 = generate_expr context e1 in
      let context = add_instruction context (Sw (r1, SP, -20)) in (* 保存r1到临时位置 *)
      let context, r2 = generate_expr context e2 in
      let context = add_instruction context (Sw (r2, SP, -24)) in (* 保存r2到临时位置 *)
      let context = add_instruction context (Lw (T0, SP, -20)) in (* 恢复r1到T0 *)
      let context = add_instruction context (Lw (T1, SP, -24)) in (* 恢复r2到T1 *)
      let context = match op with
        | Add -> 
            let context = add_instruction context (Add (T0, T0, T1)) in
            context
        | Sub -> 
            let context = add_instruction context (Sub (T0, T0, T1)) in
            context
        | Mul -> 
            let context = add_instruction context (Mul (T0, T0, T1)) in
            context
        | Div -> 
            let context = add_instruction context (Div (T0, T0, T1)) in
            context
        | Mod -> 
            let context = add_instruction context (Rem (T0, T0, T1)) in
            context
        | Lt ->
            let context = add_instruction context (Slt (T0, T0, T1)) in
            context
        | Gt ->
            let context = add_instruction context (Slt (T0, T1, T0)) in
            context
        | Le ->
            let context = add_instruction context (Slt (T0, T1, T0)) in
            let context = add_instruction context (Seqz (T0, T0)) in
            context
        | Ge ->
            let context = add_instruction context (Slt (T0, T0, T1)) in
            let context = add_instruction context (Seqz (T0, T0)) in
            context
        | Eq ->
            let context = add_instruction context (Sub (T0, T0, T1)) in
            let context = add_instruction context (Seqz (T0, T0)) in
            context
        | Ne ->
            let context = add_instruction context (Sub (T0, T0, T1)) in
            let context = add_instruction context (Snez (T0, T0)) in
            context
        | And ->
            let context = add_instruction context (Snez (T0, T0)) in
            let context = add_instruction context (Snez (T1, T1)) in
            let context = add_instruction context (And (T0, T0, T1)) in
            context
        | Or ->
            let context = add_instruction context (Snez (T0, T0)) in
            let context = add_instruction context (Snez (T1, T1)) in
            let context = add_instruction context (Or (T0, T0, T1)) in
            context in
      context, T0
  | Call (func_name, args) ->
      (* 函数调用：保存参数到寄存器，调用函数，返回值在A0 *)
      let context = match args with
        | [] -> context
        | [arg] ->
            let context, reg = generate_expr context arg in
            add_instruction context (Add (A0, reg, Zero))
        | args ->
            (* 多参数支持：将参数保存到栈上 *)
            let rec save_args ctx arg_list offset =
              match arg_list with
              | [] -> ctx
              | arg :: rest ->
                  let ctx, reg = generate_expr ctx arg in
                  let ctx = add_instruction ctx (Sw (reg, SP, offset)) in
                  save_args ctx rest (offset - 4)
            in
            save_args context args (-28) in
      let context = add_instruction context (Jal func_name) in
      context, A0
  | Assign (name, expr) ->
      (* 赋值表达式：计算右侧表达式，存储到变量，返回赋值的值 *)
      (match find_variable context name with
      | Some var_info ->
          let context, reg = generate_expr context expr in
          let context = add_instruction context (Sw (reg, SP, var_info.offset)) in
          context, reg
      | None -> failwith ("Undefined variable: " ^ name))
  | Unary (op, expr) ->
      (* 一元运算符 *)
      let context, reg = generate_expr context expr in
      let context = match op with
        | Not ->
            let context = add_instruction context (Seqz (T0, reg)) in
            context
        | Neg ->
            let context = add_instruction context (Sub (T0, Zero, reg)) in
            context
        | Pos ->
            let context = add_instruction context (Add (T0, reg, Zero)) in
            context in
      context, T0

(* 生成语句代码 *)
let rec generate_stmt context stmt =
  match stmt with
  | Return None ->
      add_instruction context (J "return")
  | Return (Some expr) ->
      let context, reg = generate_expr context expr in
      let context = add_instruction context (Add (A0, reg, Zero)) in
      add_instruction context (J "return")
  | Var_decl (name, init_expr) ->
      let context, reg = generate_expr context init_expr in
      let context = add_variable context name true in (* 默认为int类型 *)
      let var_info = List.assoc name context.variables in
      add_instruction context (Sw (reg, SP, var_info.offset))
  | Expr expr ->
      (* 表达式语句，包括函数调用和赋值 *)
      let context, _ = generate_expr context expr in
      context
  | If (cond, then_stmt, else_stmt_opt) ->
      let else_label = generate_label "else" in
      let end_label = generate_label "endif" in
      
      (* 生成条件判断代码 *)
      let context, cond_reg = generate_expr context cond in
      let context = add_instruction context (Seqz (T0, cond_reg)) in
      let context = add_instruction context (Bne (T0, Zero, else_label)) in
      
      (* 生成then分支代码 *)
      let context = generate_stmt context then_stmt in
      let context = add_instruction context (J end_label) in
      
      (* 生成else分支代码 *)
      let context = add_instruction context (Label else_label) in
      let context = match else_stmt_opt with
        | Some else_stmt -> generate_stmt context else_stmt
        | None -> context in
      
      (* 结束标签 *)
      let context = add_instruction context (Label end_label) in
      context
  | While (cond, body) ->
      let start_label = generate_label "while" in
      let end_label = generate_label "endwhile" in
      
      (* 循环开始标签 *)
      let context = add_instruction context (Label start_label) in
      
      (* 生成条件判断代码 *)
      let context, cond_reg = generate_expr context cond in
      let context = add_instruction context (Seqz (T0, cond_reg)) in
      let context = add_instruction context (Bne (T0, Zero, end_label)) in
      
      (* 生成循环体代码 *)
      let context = generate_stmt context body in
      let context = add_instruction context (J start_label) in
      
      (* 循环结束标签 *)
      let context = add_instruction context (Label end_label) in
      context
  | Block stmts ->
      List.fold_left generate_stmt context stmts
  | Break ->
      (* break语句：跳转到循环结束 *)
      add_instruction context (J "break_label")
  | Continue ->
      (* continue语句：跳转到循环开始 *)
      add_instruction context (J "continue_label")

(* 生成函数代码 *)
let generate_function context func =
  let context = { context with 
    current_function = Some func.name;
    stack_size = 24; (* 固定栈帧大小：返回地址(4) + 3个变量(12) + 临时变量(8) *)
  } in
  
  (* 函数序言 *)
  let context = add_instruction context (Label func.name) in
  let context = add_instruction context (Comment "Function prologue") in
  let context = add_instruction context (Li (T0, context.stack_size)) in
  let context = add_instruction context (Sw (RA, SP, -4)) in
  let context = add_instruction context (Sub (SP, SP, T0)) in
  
  (* 添加函数参数到变量列表 *)
  let context = List.fold_left (fun acc (param: Toyc_ast.param) ->
    add_variable acc param.name true
  ) context func.params in
  
  (* 生成函数体代码 *)
  let context = List.fold_left generate_stmt context func.body in
  
  (* 函数收尾 *)
  let context = add_instruction context (Label "return") in
  let context = add_instruction context (Comment "Function epilogue") in
  let context = add_instruction context (Li (T0, context.stack_size)) in
  let context = add_instruction context (Add (SP, SP, T0)) in
  let context = add_instruction context (Lw (RA, SP, -4)) in
  let context = add_instruction context (Jr RA) in
  
  context

(* 生成程序代码 *)
let generate_program program =
  let context = new_context () in
  let context = List.fold_left generate_function context program.functions in
  context.instructions

(* 输出完整的汇编程序 *)
let output_program program =
  let instructions = generate_program program in
  String.concat "\n" (List.map string_of_instruction instructions)