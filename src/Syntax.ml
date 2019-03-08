(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

	let boolToInt n = if n then 1 else 0

	let evalBinop op a b = match op with
		| "+" -> a + b
		| "-" -> a - b
		| "*" -> a * b
		| "/" -> a / b
		| "%" -> a mod b
		| "<" -> boolToInt (a < b)
		| ">" -> boolToInt (a > b)
		| "<=" -> boolToInt (a <= b)
		| ">=" -> boolToInt (a >= b)
		| "==" -> boolToInt (a == b)
		| "!=" -> boolToInt (a != b)
		| "&&" -> boolToInt ((a != 0) && (b != 0))
		| "!!" -> boolToInt ((a != 0) || (b != 0))

	(* Expression evaluator
		 val eval : state -> expr -> int
	 
	   Takes a state and an expression, and returns the value of the expression in 
	   the given state.
	*)
	let rec eval s e = match e with
	  | Const n				-> n
	  | Var v				-> s v
	  | Binop (op, a, b)	-> evalBinop op (eval s a)(eval s b)  
	  | _ 					-> failwith "[Expr] Unimplemented expression type"

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((s, i, o) as conf) stmt = match stmt with
		| Read v ->
			(
				match i with
					| n::i -> (Expr.update v n s), i, o
					| _ -> failwith "[Stmt] No input for Read statement"
			)
		| Write x		-> s, i, o @ [Expr.eval s x]
		| Assign (v, x)	-> (Expr.update v (Expr.eval s x) s), i, o
		| Seq (t1, t2)	-> eval (eval conf t1) t2
		| _ 			-> failwith "[Stmt] Unsupported statement"
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
