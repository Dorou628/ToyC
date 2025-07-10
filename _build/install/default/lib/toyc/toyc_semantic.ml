type var_type = Int_type | Void_type

type var_info = {
  name: string;
  var_type: var_type;
}

type func_info = {
  name: string;
  return_type: var_type;
  params: var_info list;
}

type symbol_table = {
  variables: var_info list;
  functions: func_info list;
  parent: symbol_table option;
  in_loop: bool;
}

exception Type_error of string
exception Undefined_variable of string
exception Undefined_function of string
exception Break_outside_loop
exception Continue_outside_loop

let create_table parent in_loop = {
  variables = [];
  functions = [];
  parent = parent;
  in_loop = in_loop;
}

let rec find_variable (table: symbol_table) name =
  match List.find_opt (fun (v: var_info) -> v.name = name) table.variables with
  | Some var -> var
  | None ->
      match table.parent with
      | Some parent -> find_variable parent name
      | None -> raise (Undefined_variable name)

let rec find_function (table: symbol_table) name =
  match List.find_opt (fun (f: func_info) -> f.name = name) table.functions with
  | Some func -> func
  | None ->
      match table.parent with
      | Some parent -> find_function parent name
      | None -> raise (Undefined_function name)

let add_variable (table: symbol_table) (var_info: var_info) =
  { table with variables = var_info :: table.variables }

let add_function (table: symbol_table) (func_info: func_info) =
  { table with functions = func_info :: table.functions }

let rec check_expr table = function
  | Toyc_ast.Num _ -> Int_type
  | Toyc_ast.Id name -> (find_variable table name).var_type
  | Toyc_ast.Call (name, args) ->
      let func = find_function table name in
      if List.length args <> List.length func.params then
        raise (Type_error (Printf.sprintf "Function %s expects %d arguments but got %d"
                            name (List.length func.params) (List.length args)));
      List.iter2 (fun param arg ->
        let arg_type = check_expr table arg in
        if arg_type <> param.var_type then
          raise (Type_error (Printf.sprintf "Type mismatch in argument of function %s" name))
      ) func.params args;
      func.return_type
  | Toyc_ast.Binary (_, e1, e2) ->
      let t1 = check_expr table e1 in
      let t2 = check_expr table e2 in
      if t1 <> Int_type || t2 <> Int_type then
        raise (Type_error "Binary operator requires integer operands");
      Int_type
  | Toyc_ast.Unary (op, e) ->
      let t = check_expr table e in
      (match op with
      | Toyc_ast.Not when t = Int_type -> Int_type
      | Toyc_ast.Neg when t = Int_type -> Int_type
      | Toyc_ast.Pos when t = Int_type -> Int_type
      | _ -> raise (Type_error "Unary operator requires integer operand"))
  | Toyc_ast.Assign (name, e) ->
      let var = find_variable table name in
      let e_type = check_expr table e in
      if e_type <> var.var_type then
        raise (Type_error "Assignment type mismatch");
      var.var_type

let rec check_stmt_list table stmts =
  match stmts with
  | [] -> table
  | stmt :: rest ->
      let new_table = check_stmt table stmt in
      check_stmt_list new_table rest

and check_stmt table = function
  | Toyc_ast.Block stmts ->
      let block_table = create_table (Some table) table.in_loop in
      ignore (check_stmt_list block_table stmts);
      table
  | Toyc_ast.Expr e -> 
      ignore (check_expr table e);
      table
  | Toyc_ast.If (cond, then_stmt, else_stmt_opt) ->
      if check_expr table cond <> Int_type then
        raise (Type_error "Condition must be an integer");
      ignore (check_stmt table then_stmt);
      Option.iter (fun stmt -> ignore (check_stmt table stmt)) else_stmt_opt;
      table
  | Toyc_ast.While (cond, body) ->
      if check_expr table cond <> Int_type then
        raise (Type_error "Condition must be an integer");
      let loop_table = create_table (Some table) true in
      ignore (check_stmt loop_table body);
      table
  | Toyc_ast.Return None -> table
  | Toyc_ast.Return (Some e) ->
      ignore (check_expr table e);
      table
  | Toyc_ast.Break ->
      if not table.in_loop then raise Break_outside_loop;
      table
  | Toyc_ast.Continue ->
      if not table.in_loop then raise Continue_outside_loop;
      table
  | Toyc_ast.Var_decl (name, init_expr) ->
      let init_type = check_expr table init_expr in
      let var_info = { name = name; var_type = init_type } in
      add_variable table var_info

let check_program (prog: Toyc_ast.program) =
  let table = create_table None false in
  (* 首先收集所有函数声明 *)
  let table = List.fold_left (fun acc_table (func: Toyc_ast.function_def) ->
    let param_infos = List.map (fun (param: Toyc_ast.param) ->
      { name = param.name; var_type = Int_type }
    ) func.params in
    let func_info = {
      name = func.name;
      return_type = if func.return_type then Int_type else Void_type;
      params = param_infos;
    } in
    add_function acc_table func_info
  ) table prog.functions in
  (* 然后检查每个函数的函数体 *)
  List.iter (fun (func: Toyc_ast.function_def) ->
    let param_vars = List.map (fun (param: Toyc_ast.param) ->
      { name = param.name; var_type = Int_type }
    ) func.params in
    let func_table = create_table (Some table) false in
    let func_table = List.fold_left (fun acc (param_var: var_info) -> 
         add_variable acc param_var
       ) func_table param_vars in
    ignore (check_stmt_list func_table func.body)
  ) prog.functions