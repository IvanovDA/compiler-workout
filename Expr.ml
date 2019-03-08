(* Simple expressions: syntax and semantics *)

(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
             
(* The type for the expression. Note, in regular OCaml there is no "@type..." 
   notation, it came from GT. 
*)
@type expr =
  (* integer constant *) | Const of int
  (* variable         *) | Var   of string
  (* binary operator  *) | Binop of string * expr * expr with show

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