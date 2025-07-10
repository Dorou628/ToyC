open Toyc_lib

let test_program prog =
  try
    Toyc_semantic.check_program prog;
    Printf.printf "Program is semantically correct!\n"
  with
  | Toyc_semantic.Type_error msg -> Printf.printf "Type error: %s\n" msg
  | Toyc_semantic.Undefined_variable name -> Printf.printf "Undefined variable: %s\n" name
  | Toyc_semantic.Undefined_function name -> Printf.printf "Undefined function: %s\n" name
  | Toyc_semantic.Break_outside_loop -> Printf.printf "Break statement outside loop\n"
  | Toyc_semantic.Continue_outside_loop -> Printf.printf "Continue statement outside loop\n"

let () =
  (* Test case 1: Valid program *)
  let valid_prog = {
    Toyc_ast.functions = [
      {
        name = "main";
        return_type = true;
        params = [];
        body = [
          Toyc_ast.Return (Some (Toyc_ast.Num 42))
        ]
      }
    ]
  } in
  Printf.printf "Testing valid program:\n";
  test_program valid_prog;

  (* Test case 2: Undefined variable *)
  let undefined_var_prog = {
    Toyc_ast.functions = [
      {
        name = "main";
        return_type = true;
        params = [];
        body = [
          Toyc_ast.Return (Some (Toyc_ast.Id "x"))
        ]
      }
    ]
  } in
  Printf.printf "\nTesting undefined variable:\n";
  test_program undefined_var_prog;

  (* Test case 3: Type mismatch *)
  let type_mismatch_prog = {
    Toyc_ast.functions = [
      {
        name = "main";
        return_type = true;
        params = [];
        body = [
          Toyc_ast.If (Toyc_ast.Num 42, Toyc_ast.Block [], None)
        ]
      }
    ]
  } in
  Printf.printf "\nTesting type mismatch:\n";
  test_program type_mismatch_prog;

  (* Test case 4: Break outside loop *)
  let break_outside_prog = {
    Toyc_ast.functions = [
      {
        name = "main";
        return_type = true;
        params = [];
        body = [
          Toyc_ast.Break;
          Toyc_ast.Return (Some (Toyc_ast.Num 0))
        ]
      }
    ]
  } in
  Printf.printf "\nTesting break outside loop:\n";
  test_program break_outside_prog