%{
  open Ast
  open Printf
  open Lexing
%}

%token <int> INTEGER
%token <int> LOC
%token <string> VAR
%token <string> LITERAL 
%token <char> CHANNEL
%token PLUS MINUS TIMES MODULO UNDERSCORE LPAREN RPAREN LCURLY RCURLY COMMA SEQ COLON DOT NEQUALS EQUALS TRUE FALSE CALL
       IF THEN ELSE ENDIF LAMBDA EOF DEREF UPDATE SET ISUNSET  OUTPUT ASSIGN SKIP WHILE DO END
       INT BOOL  STRING COND FUNC REF LOW HIGH ERASE CHANNEL DECLASSIFY TOP FST SND LSQBR RSQBR 
       LESSTHAN 

%type <Ast.program> program
%type <Ast.stmt> stmt
%type <Ast.exp> exp
%type <Ast.cndset> Uset

%start program
 
%%

Uset    : LCURLY RCURLY 		{VarSet.empty}
	 | LCURLY unsetcnd RCURLY	{VarSet.union $2 VarSet.empty }

unsetcnd : VAR 				{VarSet.add $1 VarSet.empty}
	 | VAR COMMA unsetcnd		{VarSet.add $1 $3}	
 

policy  : LOW						{Low}
        | HIGH						{High}
	| TOP						{Top}
        | policy ERASE policy COMMA VAR 		{Erase($1, $5, $3)}

basetype  : INT				   {BtInt}
          | BOOL			   {BtBool}
 	  | STRING			   {BtString}
          | COND			   {BtCond}
	  | LPAREN labeltype LSQBR INTEGER RSQBR RPAREN  {BtArray($4, $2)}
	  | LPAREN basetype COMMA basetype RPAREN { BtPair($2, $4)}
          | FUNC LPAREN LCURLY vardecllist RCURLY COMMA policy COMMA Uset COMMA LCURLY vardecllist RCURLY RPAREN {BtFunc($4, $7, $9, $12)}
	  | labeltype REF		   {BtRef($1)}

labeltype : basetype UNDERSCORE policy  { ($1, $3) }

vardecl   : LOC COLON labeltype   { VarLocMap.add (Mem $1) $3 VarLocMap.empty } 
          | VAR COLON labeltype	    { VarLocMap.add (Reg $1) $3 VarLocMap.empty }
	 
vardecllist: vardecl                { $1 }
	 |vardecl SEQ vardecllist   { VarLocMap.merge (fun key left right -> match left, right with
							| Some x, Some y -> None (* Error *)
							| None, right -> right
							| left, None  -> left
						      ) $1 $3 }
program: vardecllist stmtlist           		{($1, (Seq $2))} 

stmtlist : stmt 					{ [$1] }
         | stmt stmtlist				{ [$1] @ $2 }
stmt : IF bexp THEN stmtlist ELSE stmtlist ENDIF SEQ 	{ If($2, (Seq $4), (Seq $6)) }
     | SKIP SEQ			   			{ Skip }
     | VAR ASSIGN exp SEQ		    			{ Assign($1, $3)  }
     | VAR ASSIGN DECLASSIFY LPAREN exp RPAREN SEQ  	{ Declassify($1, $5)  }
     | WHILE bexp DO stmtlist   END   SEQ  		{ While($2, (Seq $4)) }
     | exp UPDATE exp SEQ			    		{ Update($1, $3) }
     | OUTPUT LPAREN CHANNEL COMMA aexp RPAREN SEQ  	{ Output($3, $5) }
     | CALL LPAREN exp RPAREN SEQ	    			{ Call($3) }
     | SET LPAREN VAR RPAREN  SEQ      			{ Set($3) }


exp : bexp 				{ $1 }
    | aexp 				{ $1 }
    | lexp                              { $1 }
    | sexp				{ $1 }
    | texp				{ $1 }
    | arrexp				{ $1 }

lexp : LPAREN LAMBDA LPAREN LCURLY vardecllist RCURLY COMMA policy COMMA Uset COMMA LCURLY vardecllist RCURLY RPAREN DOT stmtlist RPAREN UNDERSCORE policy 	{ Lam($5,$8,$10,$13,$20, (Seq $17)) }
 
bexp: TRUE			  			 { True  }
    | FALSE                        			 { False }
    | exp EQUALS exp 					 { Eq($1, $3) }
    | exp NEQUALS exp 				 	 { Neq($1, $3) }
    | aexp LESSTHAN aexp 				 { Lt($1, $3) }
    | ISUNSET LPAREN VAR RPAREN   			 { Isunset($3) }
    

aexp: 	VAR                          { Var $1}
    | INTEGER                      { Constant($1) }
    | LOC			   { Loc($1) }
    | aexp PLUS aexp 		   { Plus($1, $3) }
    | aexp MINUS aexp 		   { Plus($1, $3) }
    | aexp TIMES aexp 		   { Plus($1, $3) }
    | aexp MODULO aexp 		   { Modulo($1, $3) }
    | LPAREN DEREF exp	RPAREN	   { Deref($3) }
sexp: LITERAL			   { Literal($1) }
texp: LPAREN exp COMMA exp RPAREN  { Tuple ($2, $4) }
    | FST exp			   { Fst($2) }
    | SND exp			   { Snd($2) }
arrexp: 
    | LPAREN loclist RPAREN { Array($2) }
    |  exp LSQBR exp RSQBR { Index($1, $3) }

loclist:
    | LOC COMMA loclist		{[$1]@$3}
    | LOC			{[$1]}
    
