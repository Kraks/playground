%{
  open Syntax
%}

/* Lexemes */
%token <int> NUMERAL
%token PLUS
%token MINUS
%token TIMES
%token DIVIDE
%token UMINUS
%token POWER
%token LPAREN
%token RPAREN
%token EOF

/* precedence and associativity */
%left PLUS MINUS
%left TIMES DIVIDE
%left POWER
%nonassoc UMINUS

/* top level rule */
%start toplevel
%type <Syntax.expression> toplevel

%%

toplevel: expression EOF { $1 }
;

expression:
  | NUMERAL                       { Numeral $1}
  | expression TIMES expression   { Times ($1, $3) }
  | expression PLUS expression    { Plus ($1, $3) }
  | expression MINUS expression   { Minus ($1, $3) }
  | expression DIVIDE expression  { Divide ($1, $3) }
  | expression POWER expression  { Power ($1, $3) }
  | MINUS expression %prec UMINUS { Negate $2 }
  | LPAREN expression RPAREN      { $2 }
;
