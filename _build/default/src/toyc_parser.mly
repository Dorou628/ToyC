%{
  open Toyc_ast
%}

%token INT_TYPE VOID_TYPE
%token IF ELSE WHILE BREAK CONTINUE RETURN
%token <string> ID
%token <int> NUMBER
%token ASSIGN SEMICOLON
%token LBRACE RBRACE LPAREN RPAREN COMMA
%token OR AND
%token LT GT LE GE EQ NE
%token PLUS MINUS
%token MUL DIV MOD
%token NOT
%token EOF

%nonassoc ELSE
%right ASSIGN
%left OR
%left AND
%left EQ NE
%left LT GT LE GE
%left PLUS MINUS
%left MUL DIV MOD
%right NOT

%start <Toyc_ast.program> program

%%

program:
  | functions = list(function_def) EOF { { functions } }

function_def:
  | return_type = type_spec; name = ID;
    LPAREN; params = separated_list(COMMA, param); RPAREN;
    LBRACE; body = list(stmt); RBRACE;
    { { name; params; return_type; body } }

param:
  | INT_TYPE; name = ID { { name } }

type_spec:
  | INT_TYPE { true }
  | VOID_TYPE { false }

stmt:
  | LBRACE; stmts = list(stmt); RBRACE { Block stmts }
  | e = expr; SEMICOLON { Expr e }
  | IF; LPAREN; cond = expr; RPAREN;
    then_stmt = stmt;
    else_stmt = option(preceded(ELSE, stmt))
    { If (cond, then_stmt, else_stmt) }
  | WHILE; LPAREN; cond = expr; RPAREN; body = stmt
    { While (cond, body) }
  | BREAK; SEMICOLON { Break }
  | CONTINUE; SEMICOLON { Continue }
  | RETURN; e = option(expr); SEMICOLON { Return e }
  | INT_TYPE; name = ID; ASSIGN; init = expr; SEMICOLON
    { Var_decl (name, init) }

expr:
  | n = NUMBER { Num n }
  | id = ID { Id id }
  | name = ID; LPAREN; args = separated_list(COMMA, expr); RPAREN
    { Call (name, args) }
  | e1 = expr; op = binary_op; e2 = expr { Binary (op, e1, e2) }
  | op = unary_op; e = expr { Unary (op, e) }
  | id = ID; ASSIGN; e = expr { Assign (id, e) }
  | LPAREN; e = expr; RPAREN { e }

binary_op:
  | PLUS { Add }
  | MINUS { Sub }
  | MUL { Mul }
  | DIV { Div }
  | MOD { Mod }
  | LT { Lt }
  | GT { Gt }
  | LE { Le }
  | GE { Ge }
  | EQ { Eq }
  | NE { Ne }
  | AND { And }
  | OR { Or }

unary_op:
  | NOT { Not }
  | MINUS { Neg }
  | PLUS { Pos }