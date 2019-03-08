(* A deep embedding of simple expressions in OCaml. *)

(* Opening GT yet again. *)
open GT
       
(* Opening the substrate module for convenience. *)
open Expr

(* Shortcuts for leaf constructors *)
let ( ! ) x = Var x
let ( !? ) n = Const n

(* Implementation of operators *)
let binop op x y = Binop (op, x, y)
                         
let ( +  ) = binop "+"
let ( -  ) = binop "-"
let ( *  ) = binop "*"
let ( /  ) = binop "/"
let ( %  ) = binop "%"
let ( <  ) = binop "<"
let ( <= ) = binop "<="
let ( >  ) = binop ">"
let ( >= ) = binop ">="
let ( == ) = binop "=="
let ( != ) = binop "!="
let ( && ) = binop "&&"
let ( || ) = binop "!!"

(* Some predefined names for variables *)
let x = !"x"
let y = !"y"
let z = !"z"
let t = !"t"
                   
