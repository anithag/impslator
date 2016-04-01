open Ast

exception IllformedExpression 
exception BadProgram

let error s = (print_string ("Error: "^ s); raise BadProgram)
