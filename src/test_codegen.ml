open Toyc_lib

(* 测试简单的返回语句 *)
let test_return () =
  let program = {
    Toyc_ast.functions = [
      {
        name = "main";
        params = [];
        return_type = true; (* int类型 *)
        body = [
          Toyc_ast.Return (Some (Toyc_ast.Num 0))
        ]
      }
    ]
  } in
  
  let asm = Toyc_codegen.output_program program in
  Printf.printf "Generated assembly for return statement:\n%s\n" asm

(* 测试条件和循环语句 *)
let test_control_flow () =
  let open Toyc_ast in
  let open Toyc_codegen in
  let stmt = Block [
    Var_decl ("a", Num 42);
    Var_decl ("b", Num (-10));
    Var_decl ("c", Binary (Add, Id "a", Binary (Mul, Id "b", Num 2)));
    If (Binary (And,
        Binary (Gt, Id "a", Id "b"),
        Binary (Le, Id "c", Num 100)),
      Block [Return (Some (Num 1))],
      Some (Block [Return (Some (Num 0))]))
  ] in
  let context = create_context () in
  let context = generate_stmt context stmt in
  print_endline "Generated assembly for control flow:";
  print_endline "test_operators:";
  List.iter (fun instr -> print_endline ("        " ^ string_of_instruction instr)) context.instructions

(* 测试add函数 *)
let test_add () =
  let open Toyc_ast in
  let open Toyc_codegen in
  let func = {
    name = "add";
    params = [{ name = "x" }; { name = "y" }];
    return_type = true;
    body = [
      Var_decl ("x", Num 0);
      Var_decl ("y", Num 0);
      Return (Some (Binary (Add, Id "x", Id "y")))
    ]
  } in
  let program = { functions = [func] } in
  let asm = output_program program in
  Printf.printf "Generated assembly for add function:\n%s\n" asm

(* 测试test_control函数 *)
let test_control_func () =
  let open Toyc_ast in
  let open Toyc_codegen in
  let func = {
    name = "test_control";
    params = [{ name = "n" }];
    return_type = true;
    body = [
      Var_decl ("n", Num 0);
      Var_decl ("sum", Num 0);
      Var_decl ("i", Num 0);
      While (Binary (Lt, Id "i", Id "n"),
        Block [
          If (Binary (Eq, Binary (Mod, Id "i", Num 2), Num 0),
            Block [Expr (Assign ("sum", Binary (Add, Id "sum", Id "i")))],
            None);
          Expr (Assign ("i", Binary (Add, Id "i", Num 1)))
        ]
      );
      Return (Some (Id "sum"))
    ]
  } in
  let program = { functions = [func] } in
  let asm = output_program program in
  Printf.printf "Generated assembly for test_control function:\n%s\n" asm

(* 运行所有测试 *)
let () =
  print_endline "Running code generation tests...";
  test_return ();
  test_control_flow ();
  test_add ();
  test_control_func ()