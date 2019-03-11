(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
                                                               
(* Instruction printer *)
let printInstr instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "[X86] Unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\arg_amount" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Single instruction compilation

     compileInstr : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)

let inRegister x = match x with
  | R _ -> true
  | _ -> false

let inMemory x = match x with
  | S _ | M _ -> true
  | _ -> false

let movImpl a b = 
  if (a = b) then []
  else
    if (inMemory a) && (inMemory b)
      then [Mov (a, eax); Mov (eax, b)]
      else [Mov (a, b)]

let compSuffix op = match op with
  | "<"  -> "l"
  | "<=" -> "le"
  | ">"  -> "g"
  | ">=" -> "ge"
  | "==" -> "e"
  | "!=" -> "ne"
  | _    -> failwith "[X86] Unsupported comparator"
  
let zeroOut reg = Binop("^", reg, reg)
   
let compileCall env name arg_amount =
  let p = true in
  (*let name =
	match name.[0] with '.' -> "B" ^ String.sub name 1 (String.length name - 1) | _ -> name
  in*)
  let pushr, popr =
	List.split @@ List.map (fun r -> (Push r, Pop r)) (env#live_registers arg_amount)
  in
  let env, code =
	if arg_amount = 0
	then env, pushr @ [Call name] @ (List.rev popr)
	else
	  let rec push_args env acc = function
	  | 0 -> env, acc
	  | arg_amount -> let x, env = env#pop in
			 push_args env ((Push x)::acc) (arg_amount-1)
	  in
	  let env, pushs = push_args env [] arg_amount in
	  let pushs      =
		match name with
		| "Barray" -> List.rev @@ (Push (L arg_amount))     :: pushs
		| "Bsta"   ->
		   let x::v::is = List.rev pushs in               
		   is @ [x; v] @ [Push (L (arg_amount-2))]
		| _  -> List.rev pushs 
	  in
	  env, pushr @ pushs @ [Call name; Binop ("+", L (arg_amount*4), esp)] @ (List.rev popr)
  in
  (if p then env, code else let y, env = env#allocate in env, code @ [Mov (eax, y)])
   
let compileInstr env i =
  match i with
  | BINOP op -> (
    let b, a, env = env#pop2 in
    match op with
      | "+" | "-" | "*" ->
        if inRegister a
          then env#push a, [Binop(op, b, a)]
          else (
            if inRegister b
              then env#push b, [Binop(op, a, b)]
              else env#push a, [Mov(a, eax); Binop(op, b, eax); Mov(eax, a)]
        )
      | "/" | "%" -> 
        let result = match op with
          | "/" -> eax
          | _ -> edx
        in
        env#push a, [Mov(a, eax); Cltd; IDiv b; Mov (result, a)]
      | "&&" | "!!" ->
        (*This one could be optimised a bit*)
        env#push a, [
          zeroOut eax; zeroOut edx;
          Binop ("cmp", L 0, a); Set ("nz", "%al");
          Binop ("cmp", L 0, b); Set ("nz", "%dl");
          Binop (op, eax, edx); Mov (edx, a)
        ]
      | "<" | "<=" | ">" | ">=" | "==" | "!=" ->
        env#push a,
        if inRegister a
          then [zeroOut eax; Binop ("cmp", b, a); Set(compSuffix op, "%al"); Mov (eax, a)] 
          else [zeroOut eax; Mov (a, edx); Binop ("cmp", b, edx); Set (compSuffix op, "%al"); Mov (eax, a)]
      | _ -> failwith "[X86] Unsupported binary operator"
  )
  | CONST arg_amount ->
    let a, env = env#allocate in
    env, [Mov (L arg_amount, a)]
  | READ ->
    let a, env = env#allocate in
    env, [Call "Lread"; Mov (eax, a)]
  | WRITE ->
    let a, env = env#pop in
    env, [Push a; Call "Lwrite"; Pop eax]
  | LD v ->
    let s, env = (env#global v)#allocate in
    let name = env#loc v in
    env, movImpl (M name) s
  | ST v ->
    let s, env = (env#global v)#pop in
    let name = env#loc v in
    env, movImpl s (M name)
  | LABEL label -> env, [Label label]
  | JMP label -> env, [Jmp label]
  | CJMP(needZero, label) ->
    let s, env = env#pop in
    env, [Binop("cmp", L 0, s); CJmp(needZero, label)]
  | END -> env, []
  | CALL(name, n) -> 
    compileCall env name n
  (*| BEGIN()*)				(*<- the root of all weevil*)
    
(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)

let rec compile env p =
  match p with
    | [] -> env, []
    | i::p ->
        let env, x86p1 = compileInstr env i in
        let env, x86p2 = compile env p in
        env, x86p1 @ x86p2
    
(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
class env =
  object (self)
    val stack_slots = 0        (* maximal number of stack positions *)
    val globals     = S.empty  (* a set of global variables         *)
    val stack       = []       (* symbolic stack                    *)

    (* gets a name for a global variable *)
    method loc x = "global_" ^ x                                 

    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, arg_amount =

    let rec allocate' = function
    | []                            -> ebx     , 0
    | (S arg_amount)::_                      -> S (arg_amount+1) , arg_amount+1
    | (R arg_amount)::_ when arg_amount < num_of_regs -> R (arg_amount+1) , stack_slots
    | (M _)::s                      -> allocate' s
    | _                             -> S 0     , 1
    in
    allocate' stack

      in
      x, {< stack_slots = max arg_amount stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)

    method pop  = match stack with
      | x::stack' -> x, {< stack = stack' >}
      | _ -> failwith "[X86] Not enough items on stack (pop)"

    (* pops two operands from the symbolic stack *)
    method pop2 = match stack with
      | x::y::stack' -> x, y, {< stack = stack' >}
      | [x] -> failwith "[X86] Not enough items on stack (expected 2, got 1)"
      | _ -> failwith "[X86] Not enough items on stack (expected 2, got 0)"

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets the number of allocated stack slots *)
    method allocated = stack_slots

    (* gets all global variables *)      
    method globals = S.elements globals
	
	(* returns a list of live registers *)
	method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack
  end

(* Compiles a unit: generates x86 machine code for the stack program and surrounds it
   with function prologue/epilogue
*)
let compile_unit (env:env) scode =  
  let env, code = compile env scode in
  env, 
  ([Push ebp; Mov (esp, ebp); Binop ("-", L (word_size*env#allocated), esp)] @ 
   code @
   [Mov (ebp, esp); Pop ebp; Binop ("^", eax, eax); Ret]
  )

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm prog =
  let env, code = compile_unit (new env) (SM.compile prog) in
  let asm = Buffer.create 1024 in
  Buffer.add_string asm "\t.data\arg_amount";
  List.iter
    (fun s ->
       Buffer.add_string asm (Printf.sprintf "%s:\t.int\t0\arg_amount" s)
    )
    env#globals;
  Buffer.add_string asm "\t.text\arg_amount";
  Buffer.add_string asm "\t.globl\tmain\arg_amount";
  Buffer.add_string asm "main:\arg_amount";
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\arg_amount" @@ printInstr i))
    code;
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build stmt name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm stmt);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
