From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Data.Option
     Data.Monads.OptionMonad.


From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import Coqlib sflib.


(* From HafniumCore *)
Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import Any.
Require Import Lang.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Set Implicit Arguments.

(* FACT - simple itree *)
Module FACT.
  Definition fact (n: var) (res: var) :=
    res #= (Int.repr 1) #;
    #while n
    do (
      res #= res * n #;
      n #= n - (Int.repr 1)
    ) #;
    Return res.
    
  Definition factF: function. mk_function_tac fact ["n"] ["res"]. Defined.

  Definition fact_program: program :=
    [ ("fact", factF) ].
  
  Definition fact_modsem : ModSem := program_to_ModSem fact_program.
End FACT.


Module FACT_ITREE.
  Inductive EmptyE: Type -> Type :=
  | Eempty : EmptyE unit.
  
  Definition E := CallExternalE +' EmptyE +' GlobalE +' MemoryE +' Event.
  
  Definition fact_body (x : nat) : itree (callE nat nat +' E) nat :=
    match x with
    | 0%nat => Ret 1%nat
    | S m =>
      y <- call m ;;  (* Recursively compute [y := m!] *)
      Ret (x * y)%nat
    end.

  Definition fact_call (args: list val) : itree E (val * list val) :=
    match args with
    | [Vcomp (Vint n)] =>
      res <- rec fact_body (Z.to_nat (Int.unsigned n)) ;;
      Ret (Vcomp (Vint (Int.repr (Z.of_nat res))), args)
    | _ => Ret (Vcomp (Vint (Int.repr 0)), args)
    end.

  Definition handle_EmptyE {E: Type -> Type}
    : EmptyE ~> stateT Any (itree E) :=
    fun _ e oh =>
      match e with
      | Eempty => Ret (oh, tt)
      end.  
  
  Definition fact_modsem : ModSem :=
    mk_ModSem
      (fun s => string_dec s "fact")
      _
      (upcast tt)
      EmptyE
      handle_EmptyE
      (fun T (c: CallExternalE T) =>
         let '(CallExternal func_name args) := c in
         fact_call args
      ).
End FACT_ITREE.

Module FACT_COQ.
  Inductive EmptyE: Type -> Type :=
  | Eempty : EmptyE unit.
  
  Definition E := CallExternalE +' EmptyE +' GlobalE +' MemoryE +' Event.

  Definition handle_EmptyE {E: Type -> Type}
    : EmptyE ~> stateT Any (itree E) :=
    fun _ e oh =>
      match e with
      | Eempty => Ret (oh, tt)
      end.  
  
  Fixpoint fact (n: nat):nat :=
    match n with
    | O => 1
    | S n' => n * (fact n')
    end.

  Definition fact_call (args: list val) : itree E (val * list val) :=
    match args with
    | [Vcomp (Vint n)] =>
      let res := fact (Z.to_nat (Int.unsigned n)) in
      Ret (Vcomp (Vint (Int.repr (Z.of_nat res))), args)
    | _ => Ret (Vcomp (Vint (Int.repr 0)), args)
    end.
  
  Definition fact_modsem : ModSem :=
    mk_ModSem
      (fun s => string_dec s "fact")
      _
      (upcast tt)
      EmptyE
      handle_EmptyE
      (fun T (c: CallExternalE T) =>
         let '(CallExternal func_name args) := c in
         if string_dec func_name "fact"
         then fact_call args
         else triggerUB ""
      ).
End FACT_COQ.

Module FACTTEST.
  Definition main : stmt :=
    Put "fact 5 =" (Call "fact" [CBV (Int.repr 5)]) #;
    Put "fact 7 =" (Call "fact" [CBV (Int.repr 7)]).

  Definition f_function: function. mk_function_tac main ([]:list var) ([]:list var). Defined.

  Definition main_function: function.
    mk_function_tac main ([]:list var) ([]:list var). Defined.

  Definition program: program := [("main", main_function)].

  Definition modsems1: list ModSem :=
    [program_to_ModSem program; FACT.fact_modsem].

  Definition isem1: itree Event unit := eval_multimodule modsems1.

  Definition modsems2: list ModSem :=
    [program_to_ModSem program; FACT_ITREE.fact_modsem].

  Definition isem2: itree Event unit := eval_multimodule modsems2.

  Definition modsems3: list ModSem :=
    [program_to_ModSem program; FACT_COQ.fact_modsem].

  Definition isem3: itree Event unit := eval_multimodule modsems3.
End FACTTEST.

(* Require Import Maps. *)

(* (* MAP - itree status *) *)
(* Module MAP_ITREE. *)
(*   Inductive mapE: Type -> Type := *)
(*   | ESet (k: Z) (v: int): mapE unit *)
(*   | EGet (k: Z): mapE int *)
(*   . *)

(*   Definition E := CallExternalE +' mapE +' GlobalE +' MemoryE +' Event. *)

(*   Definition set_aux (args: list val) : itree E (val * list val) := *)
(*     match args with *)
(*     | [Vcomp (Vint k); Vcomp (Vint v)] => *)
(*       trigger (ESet (Int.unsigned k) v) ;; *)
(*       Ret (Vnull, args) *)
(*     | _ => triggerUB "set - args error" *)
(*     end *)
(*   . *)

(*   Definition get_aux (args: list val) : itree E (val * list val) := *)
(*     match args with *)
(*     | [Vcomp (Vint k)] => *)
(*       v <- trigger (EGet (Int.unsigned k));; *)
(*       Ret (Vcomp (Vint v), args) *)
(*     | _ => triggerUB "get - args error" *)
(*     end *)
(*   . *)

(*   Definition handle_mapE {E: Type -> Type} *)
(*     : mapE ~> stateT (ZMap.t int) (itree E) := *)
(*     fun _ e map => *)
(*       match e with *)
(*       | ESet k v => Ret (ZMap.set k v map, tt) *)
(*       | EGet k => Ret (map, ZMap.get k map) *)
(*       end *)
(*   . *)
  
(*   Definition map_modsem : ModSem := *)
(*     mk_ModSem *)
(*       (fun s => orb (string_dec s "get") (string_dec s "set")) *)
(*       _ *)
(*       (ZMap.init (Int.repr 0)) *)
(*       mapE *)
(*       handle_mapE *)
(*       (fun T (c: CallExternalE T) => *)
(*          let '(CallExternal func_name args) := c in *)
(*          match func_name with *)
(*          | "set" => set_aux args *)
(*          | "get" => get_aux args *)
(*          | _ => triggerUB "No map func" *)
(*          end *)
(*       ) *)
(*   . *)
  
(* End MAP_ITREE. *)

(* Module MAPTEST. *)
(*   Definition main : stmt := *)
(*     Put "init map to 0" Vnull #; *)
(*     Put "get 3 =" (Call "get" [CBV (Int.repr 3)]) #; *)
(*     Put "set 3 4" Vnull #; *)
(*     (Call "set" [CBV (Int.repr 3); CBV (Int.repr 4)]) #; *)
(*     Put "set 5 2" Vnull #; *)
(*     (Call "set" [CBV (Int.repr 5); CBV (Int.repr 2)]) #; *)
(*     Put "get 3 =" (Call "get" [CBV (Int.repr 3)]) #; *)
(*     Put "get 5 =" (Call "get" [CBV (Int.repr 5)]) #; *)
(*     Skip *)
(*   . *)

(*   Definition f_function: function. mk_function_tac main ([]:list var) ([]:list var). Defined. *)

(*   Definition main_function: function. *)
(*     mk_function_tac main ([]:list var) ([]:list var). Defined. *)

(*   Definition program: program := [("main", main_function)]. *)

(*   Definition modsems: list ModSem := *)
(*     [program_to_ModSem program; MAP_ITREE.map_modsem] *)
(*   . *)

(*   Definition isem: itree Event unit := eval_multimodule modsems. *)

(* End MAPTEST. *)
