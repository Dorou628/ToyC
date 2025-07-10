
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | WHILE
    | VOID_TYPE
    | SEMICOLON
    | RPAREN
    | RETURN
    | RBRACE
    | PLUS
    | OR
    | NUMBER of (
# 8 "src/toyc_parser.mly"
       (int)
# 23 "src/toyc_parser.ml"
  )
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
    | ID of (
# 7 "src/toyc_parser.mly"
       (string)
# 39 "src/toyc_parser.ml"
  )
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
  
end

include MenhirBasics

# 1 "src/toyc_parser.mly"
  
  open Toyc_ast

# 61 "src/toyc_parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_program) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: program. *)

  | MenhirState05 : (('s, _menhir_box_program) _menhir_cell1_type_spec _menhir_cell0_ID, _menhir_box_program) _menhir_state
    (** State 05.
        Stack shape : type_spec ID.
        Start symbol: program. *)

  | MenhirState10 : (('s, _menhir_box_program) _menhir_cell1_param, _menhir_box_program) _menhir_state
    (** State 10.
        Stack shape : param.
        Start symbol: program. *)

  | MenhirState14 : ((('s, _menhir_box_program) _menhir_cell1_type_spec _menhir_cell0_ID, _menhir_box_program) _menhir_cell1_loption_separated_nonempty_list_COMMA_param__, _menhir_box_program) _menhir_state
    (** State 14.
        Stack shape : type_spec ID loption(separated_nonempty_list(COMMA,param)).
        Start symbol: program. *)

  | MenhirState16 : (('s, _menhir_box_program) _menhir_cell1_WHILE, _menhir_box_program) _menhir_state
    (** State 16.
        Stack shape : WHILE.
        Start symbol: program. *)

  | MenhirState21 : (('s, _menhir_box_program) _menhir_cell1_LPAREN, _menhir_box_program) _menhir_state
    (** State 21.
        Stack shape : LPAREN.
        Start symbol: program. *)

  | MenhirState23 : (('s, _menhir_box_program) _menhir_cell1_ID, _menhir_box_program) _menhir_state
    (** State 23.
        Stack shape : ID.
        Start symbol: program. *)

  | MenhirState24 : (('s, _menhir_box_program) _menhir_cell1_unary_op, _menhir_box_program) _menhir_state
    (** State 24.
        Stack shape : unary_op.
        Start symbol: program. *)

  | MenhirState39 : (('s, _menhir_box_program) _menhir_cell1_expr _menhir_cell0_binary_op, _menhir_box_program) _menhir_state
    (** State 39.
        Stack shape : expr binary_op.
        Start symbol: program. *)

  | MenhirState45 : (('s, _menhir_box_program) _menhir_cell1_expr, _menhir_box_program) _menhir_state
    (** State 45.
        Stack shape : expr.
        Start symbol: program. *)

  | MenhirState47 : (('s, _menhir_box_program) _menhir_cell1_ID, _menhir_box_program) _menhir_state
    (** State 47.
        Stack shape : ID.
        Start symbol: program. *)

  | MenhirState52 : ((('s, _menhir_box_program) _menhir_cell1_WHILE, _menhir_box_program) _menhir_cell1_expr, _menhir_box_program) _menhir_state
    (** State 52.
        Stack shape : WHILE expr.
        Start symbol: program. *)

  | MenhirState53 : (('s, _menhir_box_program) _menhir_cell1_RETURN, _menhir_box_program) _menhir_state
    (** State 53.
        Stack shape : RETURN.
        Start symbol: program. *)

  | MenhirState57 : (('s, _menhir_box_program) _menhir_cell1_LBRACE, _menhir_box_program) _menhir_state
    (** State 57.
        Stack shape : LBRACE.
        Start symbol: program. *)

  | MenhirState60 : (('s, _menhir_box_program) _menhir_cell1_INT_TYPE _menhir_cell0_ID, _menhir_box_program) _menhir_state
    (** State 60.
        Stack shape : INT_TYPE ID.
        Start symbol: program. *)

  | MenhirState64 : (('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_state
    (** State 64.
        Stack shape : IF.
        Start symbol: program. *)

  | MenhirState66 : ((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expr, _menhir_box_program) _menhir_state
    (** State 66.
        Stack shape : IF expr.
        Start symbol: program. *)

  | MenhirState72 : (((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expr, _menhir_box_program) _menhir_cell1_stmt, _menhir_box_program) _menhir_state
    (** State 72.
        Stack shape : IF expr stmt.
        Start symbol: program. *)

  | MenhirState77 : (('s, _menhir_box_program) _menhir_cell1_stmt, _menhir_box_program) _menhir_state
    (** State 77.
        Stack shape : stmt.
        Start symbol: program. *)

  | MenhirState87 : (('s, _menhir_box_program) _menhir_cell1_function_def, _menhir_box_program) _menhir_state
    (** State 87.
        Stack shape : function_def.
        Start symbol: program. *)


and 's _menhir_cell0_binary_op = 
  | MenhirCell0_binary_op of 's * (Toyc_ast.binary_op)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Toyc_ast.expr)

and ('s, 'r) _menhir_cell1_function_def = 
  | MenhirCell1_function_def of 's * ('s, 'r) _menhir_state * (Toyc_ast.function_def)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_param__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_param__ of 's * ('s, 'r) _menhir_state * (Toyc_ast.param list)

and ('s, 'r) _menhir_cell1_param = 
  | MenhirCell1_param of 's * ('s, 'r) _menhir_state * (Toyc_ast.param)

and ('s, 'r) _menhir_cell1_stmt = 
  | MenhirCell1_stmt of 's * ('s, 'r) _menhir_state * (Toyc_ast.stmt)

and ('s, 'r) _menhir_cell1_type_spec = 
  | MenhirCell1_type_spec of 's * ('s, 'r) _menhir_state * (bool)

and ('s, 'r) _menhir_cell1_unary_op = 
  | MenhirCell1_unary_op of 's * ('s, 'r) _menhir_state * (Toyc_ast.unary_op)

and ('s, 'r) _menhir_cell1_ID = 
  | MenhirCell1_ID of 's * ('s, 'r) _menhir_state * (
# 7 "src/toyc_parser.mly"
       (string)
# 193 "src/toyc_parser.ml"
)

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 7 "src/toyc_parser.mly"
       (string)
# 200 "src/toyc_parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_INT_TYPE = 
  | MenhirCell1_INT_TYPE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACE = 
  | MenhirCell1_LBRACE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_RETURN = 
  | MenhirCell1_RETURN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_WHILE = 
  | MenhirCell1_WHILE of 's * ('s, 'r) _menhir_state

and _menhir_box_program = 
  | MenhirBox_program of (Toyc_ast.program) [@@unboxed]

let _menhir_action_01 =
  fun () ->
    (
# 74 "src/toyc_parser.mly"
         ( Add )
# 229 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_02 =
  fun () ->
    (
# 75 "src/toyc_parser.mly"
          ( Sub )
# 237 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_03 =
  fun () ->
    (
# 76 "src/toyc_parser.mly"
        ( Mul )
# 245 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_04 =
  fun () ->
    (
# 77 "src/toyc_parser.mly"
        ( Div )
# 253 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_05 =
  fun () ->
    (
# 78 "src/toyc_parser.mly"
        ( Mod )
# 261 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_06 =
  fun () ->
    (
# 79 "src/toyc_parser.mly"
       ( Lt )
# 269 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_07 =
  fun () ->
    (
# 80 "src/toyc_parser.mly"
       ( Gt )
# 277 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_08 =
  fun () ->
    (
# 81 "src/toyc_parser.mly"
       ( Le )
# 285 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_09 =
  fun () ->
    (
# 82 "src/toyc_parser.mly"
       ( Ge )
# 293 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_10 =
  fun () ->
    (
# 83 "src/toyc_parser.mly"
       ( Eq )
# 301 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_11 =
  fun () ->
    (
# 84 "src/toyc_parser.mly"
       ( Ne )
# 309 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_12 =
  fun () ->
    (
# 85 "src/toyc_parser.mly"
        ( And )
# 317 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_13 =
  fun () ->
    (
# 86 "src/toyc_parser.mly"
       ( Or )
# 325 "src/toyc_parser.ml"
     : (Toyc_ast.binary_op))

let _menhir_action_14 =
  fun n ->
    (
# 64 "src/toyc_parser.mly"
               ( Num n )
# 333 "src/toyc_parser.ml"
     : (Toyc_ast.expr))

let _menhir_action_15 =
  fun id ->
    (
# 65 "src/toyc_parser.mly"
            ( Id id )
# 341 "src/toyc_parser.ml"
     : (Toyc_ast.expr))

let _menhir_action_16 =
  fun name xs ->
    let args = 
# 241 "<standard.mly>"
    ( xs )
# 349 "src/toyc_parser.ml"
     in
    (
# 67 "src/toyc_parser.mly"
    ( Call (name, args) )
# 354 "src/toyc_parser.ml"
     : (Toyc_ast.expr))

let _menhir_action_17 =
  fun e1 e2 op ->
    (
# 68 "src/toyc_parser.mly"
                                         ( Binary (op, e1, e2) )
# 362 "src/toyc_parser.ml"
     : (Toyc_ast.expr))

let _menhir_action_18 =
  fun e op ->
    (
# 69 "src/toyc_parser.mly"
                            ( Unary (op, e) )
# 370 "src/toyc_parser.ml"
     : (Toyc_ast.expr))

let _menhir_action_19 =
  fun e id ->
    (
# 70 "src/toyc_parser.mly"
                              ( Assign (id, e) )
# 378 "src/toyc_parser.ml"
     : (Toyc_ast.expr))

let _menhir_action_20 =
  fun e ->
    (
# 71 "src/toyc_parser.mly"
                             ( e )
# 386 "src/toyc_parser.ml"
     : (Toyc_ast.expr))

let _menhir_action_21 =
  fun body name return_type xs ->
    let params = 
# 241 "<standard.mly>"
    ( xs )
# 394 "src/toyc_parser.ml"
     in
    (
# 39 "src/toyc_parser.mly"
    ( { name; params; return_type; body } )
# 399 "src/toyc_parser.ml"
     : (Toyc_ast.function_def))

let _menhir_action_22 =
  fun () ->
    (
# 216 "<standard.mly>"
    ( [] )
# 407 "src/toyc_parser.ml"
     : (Toyc_ast.function_def list))

let _menhir_action_23 =
  fun x xs ->
    (
# 219 "<standard.mly>"
    ( x :: xs )
# 415 "src/toyc_parser.ml"
     : (Toyc_ast.function_def list))

let _menhir_action_24 =
  fun () ->
    (
# 216 "<standard.mly>"
    ( [] )
# 423 "src/toyc_parser.ml"
     : (Toyc_ast.stmt list))

let _menhir_action_25 =
  fun x xs ->
    (
# 219 "<standard.mly>"
    ( x :: xs )
# 431 "src/toyc_parser.ml"
     : (Toyc_ast.stmt list))

let _menhir_action_26 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 439 "src/toyc_parser.ml"
     : (Toyc_ast.expr list))

let _menhir_action_27 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 447 "src/toyc_parser.ml"
     : (Toyc_ast.expr list))

let _menhir_action_28 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 455 "src/toyc_parser.ml"
     : (Toyc_ast.param list))

let _menhir_action_29 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 463 "src/toyc_parser.ml"
     : (Toyc_ast.param list))

let _menhir_action_30 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 471 "src/toyc_parser.ml"
     : (Toyc_ast.expr option))

let _menhir_action_31 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 479 "src/toyc_parser.ml"
     : (Toyc_ast.expr option))

let _menhir_action_32 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 487 "src/toyc_parser.ml"
     : (Toyc_ast.stmt option))

let _menhir_action_33 =
  fun x ->
    let x = 
# 188 "<standard.mly>"
    ( x )
# 495 "src/toyc_parser.ml"
     in
    (
# 114 "<standard.mly>"
    ( Some x )
# 500 "src/toyc_parser.ml"
     : (Toyc_ast.stmt option))

let _menhir_action_34 =
  fun name ->
    (
# 42 "src/toyc_parser.mly"
                        ( { name } )
# 508 "src/toyc_parser.ml"
     : (Toyc_ast.param))

let _menhir_action_35 =
  fun functions ->
    (
# 33 "src/toyc_parser.mly"
                                       ( { functions } )
# 516 "src/toyc_parser.ml"
     : (Toyc_ast.program))

let _menhir_action_36 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 524 "src/toyc_parser.ml"
     : (Toyc_ast.expr list))

let _menhir_action_37 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 532 "src/toyc_parser.ml"
     : (Toyc_ast.expr list))

let _menhir_action_38 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 540 "src/toyc_parser.ml"
     : (Toyc_ast.param list))

let _menhir_action_39 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 548 "src/toyc_parser.ml"
     : (Toyc_ast.param list))

let _menhir_action_40 =
  fun stmts ->
    (
# 49 "src/toyc_parser.mly"
                                       ( Block stmts )
# 556 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_41 =
  fun e ->
    (
# 50 "src/toyc_parser.mly"
                        ( Expr e )
# 564 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_42 =
  fun cond else_stmt then_stmt ->
    (
# 54 "src/toyc_parser.mly"
    ( If (cond, then_stmt, else_stmt) )
# 572 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_43 =
  fun body cond ->
    (
# 56 "src/toyc_parser.mly"
    ( While (cond, body) )
# 580 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_44 =
  fun () ->
    (
# 57 "src/toyc_parser.mly"
                     ( Break )
# 588 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_45 =
  fun () ->
    (
# 58 "src/toyc_parser.mly"
                        ( Continue )
# 596 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_46 =
  fun e ->
    (
# 59 "src/toyc_parser.mly"
                                        ( Return e )
# 604 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_47 =
  fun init name ->
    (
# 61 "src/toyc_parser.mly"
    ( Var_decl (name, init) )
# 612 "src/toyc_parser.ml"
     : (Toyc_ast.stmt))

let _menhir_action_48 =
  fun () ->
    (
# 45 "src/toyc_parser.mly"
             ( true )
# 620 "src/toyc_parser.ml"
     : (bool))

let _menhir_action_49 =
  fun () ->
    (
# 46 "src/toyc_parser.mly"
              ( false )
# 628 "src/toyc_parser.ml"
     : (bool))

let _menhir_action_50 =
  fun () ->
    (
# 89 "src/toyc_parser.mly"
        ( Not )
# 636 "src/toyc_parser.ml"
     : (Toyc_ast.unary_op))

let _menhir_action_51 =
  fun () ->
    (
# 90 "src/toyc_parser.mly"
          ( Neg )
# 644 "src/toyc_parser.ml"
     : (Toyc_ast.unary_op))

let _menhir_action_52 =
  fun () ->
    (
# 91 "src/toyc_parser.mly"
         ( Pos )
# 652 "src/toyc_parser.ml"
     : (Toyc_ast.unary_op))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AND ->
        "AND"
    | ASSIGN ->
        "ASSIGN"
    | BREAK ->
        "BREAK"
    | COMMA ->
        "COMMA"
    | CONTINUE ->
        "CONTINUE"
    | DIV ->
        "DIV"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | GE ->
        "GE"
    | GT ->
        "GT"
    | ID _ ->
        "ID"
    | IF ->
        "IF"
    | INT_TYPE ->
        "INT_TYPE"
    | LBRACE ->
        "LBRACE"
    | LE ->
        "LE"
    | LPAREN ->
        "LPAREN"
    | LT ->
        "LT"
    | MINUS ->
        "MINUS"
    | MOD ->
        "MOD"
    | MUL ->
        "MUL"
    | NE ->
        "NE"
    | NOT ->
        "NOT"
    | NUMBER _ ->
        "NUMBER"
    | OR ->
        "OR"
    | PLUS ->
        "PLUS"
    | RBRACE ->
        "RBRACE"
    | RETURN ->
        "RETURN"
    | RPAREN ->
        "RPAREN"
    | SEMICOLON ->
        "SEMICOLON"
    | VOID_TYPE ->
        "VOID_TYPE"
    | WHILE ->
        "WHILE"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_85 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_program =
    fun _menhir_stack _v ->
      let functions = _v in
      let _v = _menhir_action_35 functions in
      MenhirBox_program _v
  
  let rec _menhir_run_88 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_function_def -> _ -> _menhir_box_program =
    fun _menhir_stack _v ->
      let MenhirCell1_function_def (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_23 x xs in
      _menhir_goto_list_function_def_ _menhir_stack _v _menhir_s
  
  and _menhir_goto_list_function_def_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState87 ->
          _menhir_run_88 _menhir_stack _v
      | MenhirState00 ->
          _menhir_run_85 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_49 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_type_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ID _v_0 ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _menhir_s = MenhirState05 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INT_TYPE ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RPAREN ->
                  let _v = _menhir_action_28 () in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_param__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let name = _v in
          let _v = _menhir_action_34 name in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_param (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState10 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INT_TYPE ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | RPAREN ->
              let x = _v in
              let _v = _menhir_action_38 x in
              _menhir_goto_separated_nonempty_list_COMMA_param_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_param_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState10 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState05 ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_11 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_param -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_param (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_39 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_param_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_08 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_type_spec _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_29 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_param__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_param__ : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_type_spec _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_param__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | RETURN ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | NUMBER _v_0 ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState14
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | LBRACE ->
              _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | INT_TYPE ->
              _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | IF ->
              _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | ID _v_1 ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState14
          | CONTINUE ->
              _menhir_run_67 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | BREAK ->
              _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
          | RBRACE ->
              let _v_2 = _menhir_action_24 () in
              _menhir_run_82 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_15 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_WHILE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState16 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_17 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_52 () in
      _menhir_goto_unary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_unary_op : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_unary_op (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
      | NUMBER _v_0 ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState24
      | NOT ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
      | MINUS ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
      | LPAREN ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
      | ID _v_1 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState24
      | _ ->
          _eRR ()
  
  and _menhir_run_18 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let n = _v in
      let _v = _menhir_action_14 n in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState14 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState57 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState77 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState66 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState72 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState64 ->
          _menhir_run_65 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState60 ->
          _menhir_run_61 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState53 ->
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState16 ->
          _menhir_run_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState47 ->
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState45 ->
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState23 ->
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState39 ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState24 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_74 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let e = _v in
          let _v = _menhir_action_41 e in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState52 ->
          _menhir_run_81 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState14 ->
          _menhir_run_77 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState77 ->
          _menhir_run_77 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState57 ->
          _menhir_run_77 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState72 ->
          _menhir_run_73 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState66 ->
          _menhir_run_71 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_81 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_WHILE, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, cond) = _menhir_stack in
      let MenhirCell1_WHILE (_menhir_stack, _menhir_s) = _menhir_stack in
      let body = _v in
      let _v = _menhir_action_43 body cond in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_77 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | RETURN ->
          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | PLUS ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | NUMBER _v_0 ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState77
      | NOT ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | MINUS ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | LPAREN ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | LBRACE ->
          _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | INT_TYPE ->
          _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | IF ->
          _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | ID _v_1 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState77
      | CONTINUE ->
          _menhir_run_67 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | BREAK ->
          _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
      | RBRACE ->
          let _v_2 = _menhir_action_24 () in
          _menhir_run_78 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2
      | _ ->
          _eRR ()
  
  and _menhir_run_53 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState53 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NUMBER _v ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | NOT ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | SEMICOLON ->
          let _v = _menhir_action_30 () in
          _menhir_goto_option_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_19 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_50 () in
      _menhir_goto_unary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_20 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_51 () in
      _menhir_goto_unary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_21 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState21 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NUMBER _v ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | NOT ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_22 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState23 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | RPAREN ->
              let _v = _menhir_action_26 () in
              _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _v
          | _ ->
              _eRR ())
      | ASSIGN ->
          let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState47 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND | COMMA | DIV | EQ | GE | GT | LE | LT | MINUS | MOD | MUL | NE | OR | PLUS | RPAREN | SEMICOLON ->
          let id = _v in
          let _v = _menhir_action_15 id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_ID -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_ID (_menhir_stack, _menhir_s, name) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_16 name xs in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_option_expr_ : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_RETURN -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_RETURN (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_46 e in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_57 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | RETURN ->
          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | PLUS ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | NUMBER _v ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState57
      | NOT ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | MINUS ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | LPAREN ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | LBRACE ->
          _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | INT_TYPE ->
          _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | IF ->
          _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | ID _v ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState57
      | CONTINUE ->
          _menhir_run_67 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | BREAK ->
          _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState57
      | RBRACE ->
          let _v = _menhir_action_24 () in
          _menhir_run_79 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_58 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_INT_TYPE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ASSIGN ->
              let _menhir_s = MenhirState60 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | PLUS ->
                  _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | NUMBER _v ->
                  _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | NOT ->
                  _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ID _v ->
                  _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_63 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState64 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_67 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_45 () in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_69 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_44 () in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_79 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_LBRACE -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LBRACE (_menhir_stack, _menhir_s) = _menhir_stack in
      let stmts = _v in
      let _v = _menhir_action_40 stmts in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_78 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_stmt -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_stmt (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_25 x xs in
      _menhir_goto_list_stmt_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_list_stmt_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState14 ->
          _menhir_run_82 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState57 ->
          _menhir_run_79 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState77 ->
          _menhir_run_78 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_82 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_type_spec _menhir_cell0_ID, _menhir_box_program) _menhir_cell1_loption_separated_nonempty_list_COMMA_param__ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_loption_separated_nonempty_list_COMMA_param__ (_menhir_stack, _, xs) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, name) = _menhir_stack in
      let MenhirCell1_type_spec (_menhir_stack, _menhir_s, return_type) = _menhir_stack in
      let body = _v in
      let _v = _menhir_action_21 body name return_type xs in
      let _menhir_stack = MenhirCell1_function_def (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOID_TYPE ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState87
      | INT_TYPE ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState87
      | EOF ->
          let _v_0 = _menhir_action_22 () in
          _menhir_run_88 _menhir_stack _v_0
      | _ ->
          _eRR ()
  
  and _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_48 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_73 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expr, _menhir_box_program) _menhir_cell1_stmt -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let x = _v in
      let _v = _menhir_action_33 x in
      _menhir_goto_option_preceded_ELSE_stmt__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_option_preceded_ELSE_stmt__ : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expr, _menhir_box_program) _menhir_cell1_stmt -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_stmt (_menhir_stack, _, then_stmt) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, cond) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let else_stmt = _v in
      let _v = _menhir_action_42 cond else_stmt then_stmt in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_71 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _menhir_s = MenhirState72 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT_TYPE ->
              _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONTINUE ->
              _menhir_run_67 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | BREAK | CONTINUE | ID _ | IF | INT_TYPE | LBRACE | LPAREN | MINUS | NOT | NUMBER _ | PLUS | RBRACE | RETURN | WHILE ->
          let _v = _menhir_action_32 () in
          _menhir_goto_option_preceded_ELSE_stmt__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_26 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_01 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_binary_op : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_binary_op (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
      | NUMBER _v_0 ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState39
      | NOT ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
      | MINUS ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
      | LPAREN ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState39
      | ID _v_1 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState39
      | _ ->
          _eRR ()
  
  and _menhir_run_27 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_13 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_28 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_11 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_29 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_03 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_30 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_05 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_31 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_02 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_32 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_06 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_33 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_08 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_34 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_07 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_35 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_09 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_36 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_10 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_37 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_04 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_38 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_12 () in
      _menhir_goto_binary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_65 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState66 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT_TYPE ->
              _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONTINUE ->
              _menhir_run_67 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | PLUS ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_61 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_INT_TYPE _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, name) = _menhir_stack in
          let MenhirCell1_INT_TYPE (_menhir_stack, _menhir_s) = _menhir_stack in
          let init = _v in
          let _v = _menhir_action_47 init name in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_56 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_RETURN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let x = _v in
          let _v = _menhir_action_31 x in
          _menhir_goto_option_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_51 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_WHILE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState52 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT_TYPE ->
              _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONTINUE ->
              _menhir_run_67 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | PLUS ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_49 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_20 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_48 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RPAREN | SEMICOLON ->
          let MenhirCell1_ID (_menhir_stack, _menhir_s, id) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_19 e id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_44 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState45 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_36 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState45 ->
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState23 ->
          _menhir_run_41 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_46 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expr -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_37 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_41 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_ID -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let x = _v in
      let _v = _menhir_action_27 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _v
  
  and _menhir_run_40 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_expr _menhir_cell0_binary_op as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RPAREN | SEMICOLON ->
          let MenhirCell0_binary_op (_menhir_stack, op) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_17 e1 e2 op in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_25 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_unary_op as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RPAREN | SEMICOLON ->
          let MenhirCell1_unary_op (_menhir_stack, _menhir_s, op) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_18 e op in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOID_TYPE ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | INT_TYPE ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | EOF ->
          let _v = _menhir_action_22 () in
          _menhir_run_85 _menhir_stack _v
      | _ ->
          _eRR ()
  
end

let program =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_program v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
