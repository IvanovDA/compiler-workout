open GT       
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)               

let evalInstruction conf instr =
	let (stack, (s, i, o)) = conf in
	match instr with
		| BINOP op -> (
			match stack with
				| b :: a :: stack -> [Syntax.Expr.evalBinop op a b] @ stack, (s, i, o)
				| a -> failwith (Printf.sprintf "[SM] Only one value on stack for binop %s" op)
				| [] -> failwith (Printf.sprintf "[SM] No values on stack for binop %s" op)
		)
		| CONST n -> [n] @ stack, (s, i, o)
		| READ -> (
			match i with
				| n :: i -> [n] @ stack, (s, i, o)
				| _ -> failwith "[SM] No input data for READ instruction"
		)
		| WRITE -> (
			match stack with
				| n :: stack -> stack, (s, i, o @ [n])
				| _ -> failwith "[SM] Empty stack on WRITE instruction"
		)
		| LD v -> [s v] @ stack, (s, i, o)
		| ST v -> (
			match stack with
				| n :: stack -> stack, ((Syntax.Expr.update v n s), i, o)
				| _ -> failwith "[SM] Empty stack on ST instruction"
		)
		| _ -> failwith "[SM] Unsupported instruction"

let eval conf p = List.fold_left evalInstruction conf p

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileExpr t = match t with
  | Syntax.Expr.Const n				-> [CONST n]
  | Syntax.Expr.Var v				-> [LD v]
  | Syntax.Expr.Binop (op, a, b)	-> (compileExpr a) @ (compileExpr b) @ [BINOP op]

let rec compile p = match p with
  | Syntax.Stmt.Read v			-> [READ; ST v]
  | Syntax.Stmt.Write x			-> (compileExpr x) @ [WRITE]
  | Syntax.Stmt.Assign (v, x)	-> (compileExpr x) @ [ST v]
  | Syntax.Stmt.Seq (p1, p2)	-> (compile p1) @ (compile p2)