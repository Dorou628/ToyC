(* ToyC 编译器主程序 *)
open Toyc_lib

let () =
  try
    (* 从标准输入读取源代码 *)
    let input = In_channel.input_all stdin in
    let lexbuf = Lexing.from_string input in
    
    (* 词法和语法分析 *)
    let ast = Toyc_parser.program Toyc_lexer.token lexbuf in
    
    (* 语义分析 *)
    let _ = Toyc_semantic.check_program ast in
    
    (* 代码生成 *)
    let asm_code = Toyc_codegen.output_program ast in
    
    (* 输出到标准输出 *)
    print_string asm_code
    
  with
    | Toyc_parser.Error ->
        Printf.eprintf "Syntax error\n";
        exit 1
    | Failure msg ->
        Printf.eprintf "Error: %s\n" msg;
        exit 1
    | exn ->
        Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string exn);
        exit 1