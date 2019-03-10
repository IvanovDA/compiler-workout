(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
       
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
      | Const n          -> n
      | Var v            -> s v
      | Binop (op, a, b) -> evalBinop op (eval s a)(eval s b)  
      | _                -> failwith "[Expr] Unimplemented expression type"
      
    let ostapOpToBinop op = ostap(- $(op)), (fun x y -> Binop (op, x, y))
      
    (* Statement parser *)
    ostap (
      expr:
        !(Util.expr
        (fun x -> x)
        (
          Array.map (fun (a, ops) -> a, List.map ostapOpToBinop ops)
          [|
            `Lefta, ["!!"];
            `Lefta, ["&&"];
            `Nona , ["=="; "!="; "<="; ">="; "<"; ">"];
            `Lefta, ["+"; "-"];
            `Lefta, ["*"; "/"; "%"];
          |]
        )
        primary
      );
      primary: v:IDENT {Var v} | n:DECIMAL {Const n} | -"(" expr -")"
    )
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t with show

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
      | Write x            -> s, i, o @ [Expr.eval s x]
      | Assign(v, x)       -> (Expr.update v (Expr.eval s x) s), i, o
      | Seq(t1, t2)        -> eval (eval conf t1) t2
      | Skip               -> conf
      | If(cond, p1, p2)   -> if (Expr.eval s cond != 0) then eval conf p1 else eval conf p2
      | While(cond, body)  -> eval conf (if (Expr.eval s cond != 0) then Seq(body, While(cond, body)) else Skip)
      | Repeat(body, cond) ->
        let (s, _, _) as conf = eval conf body in
        eval conf (if (Expr.eval s cond == 0) then Repeat(body, cond) else Skip)
      | _           -> failwith "[Stmt] Unsupported statement"
      
    (* Statement parser *)

    ostap (
      else_branch:
          "fi" {Skip}
        | "else" body:!(parse) "fi" {body}
        | "elif" cond:!(Expr.expr) "then" s1:!(parse) s2:!(else_branch) {If(cond, s1, s2)};
    
      stmt:
          v:IDENT ":=" e:!(Expr.expr) {Assign(v, e)}
        | "read" "(" x:IDENT ")" {Read x}
        | "write" "(" e:!(Expr.expr) ")" {Write e}
        | "if" cond:!(Expr.expr) "then" s1:!(parse) s2:!(else_branch) {If(cond, s1, s2)}
        | "while" cond:!(Expr.expr) "do" body:!(parse) "od" {While(cond, body)}
        | "for" init:!(stmt) "," cond:!(Expr.expr) "," step:!(stmt) "do" body:!(parse) "od" {Seq(init, While(cond, Seq(body, step)))}
        | "repeat" body:!(parse) "until" cond:!(Expr.expr) {Repeat(body, cond)}
        | "skip" {Skip};
            
      parse: s:stmt ";" rest:parse {Seq(s, rest)} | stmt
    )
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
