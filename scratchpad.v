From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.

Local Open Scope string_scope.

Local Open Scope Z_scope.

Local Open Scope list_scope.

(* Definitions *)

(* TODO: Maybe change store / heap to use some/none options *)
(* Seems heap will definitley need it ... *)

(* Heap allocation -- create an empty reference to name in heap storage
    ??? Empty reference -- return 0 or none option??
   
   Heap free -- find the heap memory cell with the passed name,
                update the heap memory to remove the reference
                if there is no reference by that name -- safe conversion?
   
   Heap assign -- find the memory reference with the passed name,
                  update the memory cell's value with the passed value,
                  if there is no reference by that name -- safe conversion?
*)
   
Definition ident := string.

Definition store : Type := ident -> Z.

Definition heap : Type := ident -> Z.

Definition update (x : ident) (v : Z) (s : store) : store :=
 fun y => if string_dec x y then v else s y.
 
Definition update_heap (x : ident) (v : Z) (h : heap) : heap :=
fun y => if string_dec x y then v else h y.

(* Type Definitions *)

(* TODO: Do I need / want a separate expression to refer to a memory reference? 

Inductive mexp : Type :=
  | REF (x : ident).              (* Memory reference expression *)*)
  
Inductive aexp : Type :=
  | CONST (n : Z)                    (* A constant number *)
  | VAR (x : ident)                  (* A variable from the store *)  
(*  | DEREF (m : mexp)                 (* A variable from the heap *) *)
  | DEREF (x : ident)                 (* A variable from the heap *)
  | PLUS (a1 : aexp) (a2 : aexp)      (* A sum of two expressions *)
  | MINUS (a1 : aexp) (a2 : aexp).    (* A difference of two expressions *)
  
Inductive bexp : Type :=
  | TRUE                                    (* Always true *)
  | FALSE                                   (* Always false *)  
  | EQUAL (a1 : aexp) (a2 : aexp)            (* Whether a1 == a2 *) 
  | LESSEQUAL (a1 : aexp) (a2 : aexp)        (* Whether a1 <= a2 *)
  | NOT (b1 : bexp)                          (* Boolean negation *)
  | AND (b1 : bexp) (b2 : bexp).             (* Boolean conjuntion *)
  
Inductive com : Type :=
  | SKIP                                            (* Do nothing *)
  | ASSIGN (x : ident) (a : aexp)                   (* Aexp assignment -- var = a *)
  | ALLOC (x : ident)                               (* Heap allocate a memory cell named 'x' *)
  | FREE (x : ident)                                (* Heap free a memory cell named 'x' *)
  | MEMASSIGN (x : ident) (a : aexp)                (* Mexp assigment -- ref = a *)
  | SEQ (c1 : com) (c2 : com)                        (* sequence c1; c2 *)
  | IFTHENELSE (b : bexp) (c1 : com) (c2 : com)     (* Conditional : if b then c1 else c2 *)
  | WHILE (b : bexp) (c1 : com).                     (* loop while b do c1 done *)
  
(* Denotational Semantics *)

Fixpoint aeval (s : store) (h : heap) (a : aexp) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | DEREF x => h x
  | PLUS a1 a2 => aeval s h a1 + aeval s h a2
  | MINUS a1 a2 => aeval s h a1 + aeval s h a2
  end.
  
  

Fixpoint beval (s : store) (h : heap) (b : bexp) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval s h a1 =? aeval s h a2
  | LESSEQUAL a1 a2 => aeval s h a1 <=? aeval s h a2
  | NOT b1 => negb (beval s h b1)
  | AND b1 b2 => beval s h b1 && beval s h b2
  end.


  

(* TODO: 
     Next steps:
         Derived forms
         Infix
         Big / Small step semantics for commands
         Lemmas
         Meta Properties
         Proofs
         
        Then, Compil
        
        Sequences?
 *)