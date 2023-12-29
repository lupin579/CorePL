%token <string> ID
%token LET
%token EQUALS
%token IN
%token PLUS
%token TIMES 
%token LPAREN
%token RPAREN
%token <int> INT
%token TRUE
%token FALSE
%token EOF
%token LEQ
%token IF
%token THEN
%token ELSE

(* the left are the association *)
(* lower precedence *)
%nonassoc IN
%nonassoc ELSE
%left LEQ
%left PLUS
%left TIMES
(* higher precedence *)

%start <Ast.expr> prog

%%

prog:
 | e = expr; EOF { e }
  ;

expr:
  | x = ID { Var x }
  | i = INT { Int i }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | e1 = expr; PLUS; e2 = expr { Binop (Add, e1, e2) }
  | e1 = expr; TIMES; e2 = expr { Binop (Mult, e1 ,e2) }
  | e1 = expr; LEQ; e2 =expr { Binop (Leq, e1, e2) }
  | LPAREN; e = expr; RPAREN { e }
  | LET; x = ID; EQUALS; e1 = expr; IN; e2 = expr { Let (x, e1, e2) }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { If (e1, e2, e3) }
  ;
