(*
 * Copyright 2020 Youngju Song
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Structures.Foldable
     Structures.Reducible
     Data.List.

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
Require Import sflib.

Require Import ClassicalDescription.
About excluded_middle_informative.

(** From CompCert *)
Require Import AST.
Require Import Memory.
Require Import Integers.
(* Require Import Floats. *)
Require Import Values.
Require Import LangType Op.

(* From HafniumCore *)
Require Import Lang Any.
Import LangNotations.

(* Require Import Nat. *)
(* Require Import Coq.Arith.PeanoNat. *)
(* Require Import Coq.NArith.BinNat. *)
(* Require Import Coq.NArith.Nnat. *)
(* Require Import BitNat. *)
Require Import BinInt.

Local Open Scope N_scope.

Set Implicit Arguments.


Module LoadStore.

  Definition main x sum: stmt :=
    sum #= Vlong Int64.zero#;
        Alloc x (Int64.repr 3) #;
        Put "x :=" x#;
        (x @ Int64.zero #:= Int64.repr 10)#;
        (x @ Int64.one #:= Int64.repr 20)#;
        (x @ (Int64.repr 2) #:= Int64.repr 30)#;
        Put "sum :=" sum#;
        sum #= sum + (x #@ Int64.zero)#;
        Put "sum :=" sum#;
        sum #= sum + (x #@ Int64.one)#;
        Put "sum :=" sum#;
        sum #= sum + (x #@ (Int64.repr 2))#;
        Put "sum :=" sum#;
        Skip
  .

  Definition function: function. mk_function_tac main ([]: list var) ["x" ; "sum"]. Defined.

  Definition program: program := [("main", function)].

  (* Extraction "LangTest.ml" load_store_program. *)
  (* Check (eval_whole_program program). *)

End LoadStore.

Module IntPtr.

  Definition main p i q res: stmt :=
    p #= Vptr 2%positive (Ptrofs.repr 400) #;
    Put "p :=" p#;
    (p @ Int64.zero #:= Int64.repr 10)#;
    i #= Cast p tint #;
    Put "i :=" i#;
    q #= Cast i tptr #;
    Put "q :=" q#;
    res #= (q #@ Int64.zero) #;
    Put "res: " res#;
    Skip.

  Definition function: function. mk_function_tac main ([]: list var) ["p" ; "i" ; "q" ; "res"]. Defined.

  Definition program: Lang.program := [("main", function)].

  (* Extraction "LangTest.ml" load_store_program. *)
  (* Check (eval_whole_program program). *)

End IntPtr.

Section TMP.
  Variable a: var.
  Variable b: val.
  Check (Var a).
  Check (Val b).
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.
  Check ((Var a) + (Val b)).
End TMP.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Module CBVCBR.
  Definition f x: stmt :=
    x #= (Int.repr 10)
  .

  Definition main x: stmt :=
    x #= (Int.repr 0) #;
      (Call "f" [CBV x]) #;
      Put "CBV " x #;
      (Call "f" [CBR x]) #;
      Put "CBR " x
  .

  Definition f_function: function. mk_function_tac f ["x"] ([]:list var). Defined.

  Definition main_function: function.
    mk_function_tac main ([]:list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].
End CBVCBR.
  
Module Rec.

  Definition f x y r: stmt :=
    (#if x
      then (y #= (x - (Vint Int.one)) #;
              r #= (Call "f" [CBV y]) #;
              r #= r + x)
      else (r #= (Vint Int.zero))
    )
      #;
      Return r
  .

  Definition f_function: function. mk_function_tac f ["x"] ["local0" ; "local1"]. Defined.

  Definition main x r: stmt :=
    x #= (Vint (Int.repr 10)) #;
      r #= (Call "f" [CBV x]) #;
      Put "" r
  .

  Definition main_function: function.
    mk_function_tac main ([]:list var) ["local0" ; "local1"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Rec.



Module MutRec.

  Definition f x y r: stmt :=
    (#if x
      then (y #= (x - Int.one) #;
              r #= (Call "g" [CBV y]) #;
              r #= r + x)
      else (r #= Int.zero)
    )
      #;
      Return r
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #= (x - Int.one) #;
              r #= (Call "f" [CBV y]) #;
              r #= r + x)
      else (r #= Int.zero)
    )
      #;
      Return r
  .

  Definition f_function: function. mk_function_tac f ["x"] ["local0" ; "local1"]. Defined.
  Definition g_function: function. mk_function_tac g ["x"] ["local0" ; "local1"]. Defined.

  Definition program: program := [("main", Rec.main_function) ;
                                    ("f", f_function) ;
                                    ("g", g_function)].
End MutRec.



(* YJ: if we just use "r", not "unused", something weird will happen *)
(* TODO: address it better *)
Module Move.
  Definition f (x accu y unused: var): stmt :=
    (#if x
      then (y #= (x - Int.one) #;
              (* Put "before call" accu #; *)
              unused #= (Call "f" [CBV y ; CBR accu]) #;
              (* Put "after call" accu #; *)
              accu #= accu + x #;
                               Skip
           )
      else
        (accu #= Int.zero)
    )
      #;
      Return (Int.repr 7777)
  .

  Definition main x accu unused: stmt :=
    x #= (Int.repr 10) #;
      accu #= (Int.repr 1000) #;
      unused #= (Call "f" [CBV x ; CBR accu]) #;
      Put "" accu
  .

  Definition f_function: function. mk_function_tac f ["x" ; "accu"]
                                                   ["local0" ; "local1"]. Defined.
  Definition main_function: function.
    mk_function_tac main ([]:list var) ["local0" ; "local1" ; "local2"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Move.





Module CoqCode.

  Definition coqcode: list val -> (val * list val) :=
    (fun v =>
       match v with
       | hd :: _ => if excluded_middle_informative (exists w, w * w = hd)
                   then (Vtrue, nil)
                   else (Vfalse, nil)
       | _ => (Vfalse, nil)
       end).

  (* Extract Constant excluded_middle_informative => "true". (* YJ: To avouid crash *) *)
  (* Extract Constant coqcode => "fun _ -> print_endline ""Is Prop true?"" ; *)
  (*                                     if (read_int() = 0) then coq_Vtrue else coq_Vfalse *)
  (*                                     ". *)
  Extract Constant coqcode => "fun _ -> (Lang.coq_Vtrue, [])".

  Definition main x: stmt :=
    x #= (Int.repr 25) #;
      (#if (CoqCode [CBV x] coqcode)
        then Put "" (Int.repr 555)
        else Put "" (Int.repr 666))
  .

  Definition main_function: function.
    mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function)].

End CoqCode.


Module CoqCodeCBR.

  Definition coqcode: list val -> (val * list val) :=
    (fun v =>
       match v with
       | hd :: nil => (Vfalse, [(Int.repr 50): val])
       | _ => (Vfalse, nil)
       end).

  Definition main x: stmt :=
    x #= (Int.repr 0) #;
      (CoqCode [CBR x] coqcode) #;
      #assume (x == (Int.repr 50)) #;
      Put "Test(CoqCodeCBR) passed" Vnull #;
      Skip
  .

  Definition main_function: function.
    mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function)].

  Definition modsems: list ModSem :=
    List.map program_to_ModSem [program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End CoqCodeCBR.

Module Control.

  Definition f ctrl ret iter: stmt :=
    iter #= (Int.repr 10) #;
         ret #= (Int.repr 0) #;
         (* Put "" ctrl #; *)
         (* Put "" iter #; *)
         (* Put "" ret #; *)
         (* Put "" 7777777 #; *)
         #while iter
         do (
           iter #= iter - (Int.repr 1)#;
                                      (* 0 --> break *)
                                      (* 1 --> continue *)
                                      (* 2 --> return *)
                                      (* 3 --> normal *)
                                      #if ctrl == (Int.repr 0) then Break else Skip #;
                                                                                    (* Put "" 1111 #; *)
                                                                                    ret #= ret + (Int.repr 1) #;
                                                                                                              #if ctrl == (Int.repr 1) then Continue else Skip #;
                                                                                                                                                               (* Put "" 2222 #; *)
                                                                                                                                                               ret #= ret + (Int.repr 10) #;
                                                                                                                                                                                          #if ctrl == (Int.repr 2) then (Return (ret + (Int.repr 100))) else Skip #;
                                                                                                                                                                                                                                                                  (* Put "" 3333 #; *)
                                                                                                                                                                                                                                                                  ret #= ret + (Int.repr 1000) #;

                                                                                                                                                                                                                                                                                               Skip
         ) #;
         Return ret
  .

  Definition f_function: function. mk_function_tac f ["ctrl"] ["local0" ; "local1"]. Defined.

  Definition main r: stmt :=
    r #= (Call "f" [CBV (Int.repr 0)]) #; #assume (r == (Int.repr 0)) #;
      r #= (Call "f" [CBV (Int.repr 1)]) #; #assume (r == (Int.repr 10)) #;
      r #= (Call "f" [CBV (Int.repr 2)]) #; #assume (r == (Int.repr 111)) #;
      r #= (Call "f" [CBV (Int.repr 3)]) #; #assume (r == (Int.repr 10110)) #;
      Skip
  .

  Definition main_function: function. mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Control.




Module DoubleReturn.

  Definition f : stmt :=
    Return (Int.repr 0) #; Return (Int.repr 1)
  .

  Definition f_function: function. mk_function_tac f ([]: list var) ([]: list var). Defined.

  Definition main r :=
    r #= (Call "f" []) #;
      #assume (r == (Int.repr 0)) #;
      Skip
  .

  Definition main_function: function. mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End DoubleReturn.




Module MultiCore.

  Definition main (n: int): stmt :=
    Put "" (n + (Int.repr 1)) #;
        Put "" (n + (Int.repr 2)) #;
        Yield #;
        Put "" (n + (Int.repr 3)) #;
        Put "" (n + (Int.repr 4)) #;
        Yield #;
        Put "" (n + (Int.repr 5)) #;
        Put "" (n + (Int.repr 6)) #;
        Skip
  .

  Definition main_function (n: int): function.
    mk_function_tac (main n) ([]: list var) ([]: list var). Defined.

  Definition program n: program := [("main", main_function n) ].

  Definition programs: list Lang.program :=
    [program (Int.repr 0) ; program (Int.repr 10); program (Int.repr 20)].
  
End MultiCore.





Module MultiCore2.

  Definition observer i: stmt :=
    i #= (Int.repr 20) #;
      #while i
      do (
        i #= i - (Int.repr 1) #;
                              #assume ("GVAR" % (Int.repr 2) == (Int.repr 0)) #;
                              Yield
      ) #;
      #if "GVAR" == (Int.repr 0) then AssumeFail else Skip #; (* Test if GlobalE actually worked *)
                                                           Put "Test(MultiCore2) passed" Vnull
  .

  Definition adder i: stmt :=
    i #= (Int.repr 20) #;
      #while i
      do (
        i #= i - (Int.repr 1) #;
                              "GVAR" #= "GVAR" + (Int.repr 1) #;
                                                              "GVAR" #= "GVAR" + (Int.repr 1) #;
                                                                                              Yield
      )
  .

  (* Definition main: stmt := *)
  (*   "GVAR" #:= 10 #; Yield *)
  (* . *)

  Definition observerF: function. mk_function_tac observer ([]: list var) (["i"]). Defined.
  Definition adderF: function. mk_function_tac adder ([]: list var) (["i"]). Defined.
  (* Definition mainF: function. mk_function_tac main ([]: list var) ([]: list var). Defined. *)

  Definition observerP: program := [("main", observerF) ].
  Definition adderP: program := [("main", adderF) ].
  (* Definition mainP: program := [("main", mainF) ]. *)

  (* Definition programs: list program := [ observerP ; adderP ; adderP ; mainP ]. *)
  Definition programs: list program := [ observerP ; adderP ; adderP ].

  Definition sem :=
    ITree.ignore
      (interp_GlobalE (round_robin (List.map eval_single_program programs)) []).

End MultiCore2.






Module MultiCoreMPSC.

  Definition producer i: stmt :=
    i #= (Int.repr 10) #;
      #while i
      do (
        Debug "PRODUCER: " i #;
              #if "GVAR" == (Int.repr 0)
               then ("GVAR" #= i #; i #= i - (Int.repr 1))
               else Skip #;
                         Yield
      ) #;
      "SIGNAL" #= "SIGNAL" + (Int.repr 1)
  .

  Definition consumer s: stmt :=
    s #= (Int.repr 0) #;
      #while true
      do (
        Debug "CONSUMER: " s #;
              #if "GVAR" == (Int.repr 0)
               then Skip
               else s #= s + "GVAR" #;
                                    "GVAR" #= (Int.repr 0)
                                    #;
                                    #if "SIGNAL" == (Int.repr 2) then Break else Skip #;
                                                                                      Yield
      ) #;
      (* Put "" s #; *)
      #assume (s == (Int.repr 110)) #;
      Put "Test(MultiCore3) passed" Vnull
  .

  Definition producerF: function. mk_function_tac producer ([]: list var) (["i"]). Defined.
  Definition consumerF: function. mk_function_tac consumer ([]: list var) (["s"]). Defined.

  Definition producerP: program := [("main", producerF) ].
  Definition consumerP: program := [("main", consumerF) ].

  Definition programs: list program := [ producerP ; consumerP ; producerP ].

  Definition sem :=
    ITree.ignore
      (interp_GlobalE (round_robin (List.map eval_single_program programs)) []).

End MultiCoreMPSC.



Module MultiModule.
  Inductive EmptyE: Type -> Type :=
  | Eempty : EmptyE unit.
  
  Definition E := CallExternalE +' EmptyE +' GlobalE +' MemoryE +' Event.

  Definition handle_EmptyE {E: Type -> Type}
    : EmptyE ~> stateT Any (itree E) :=
    fun _ e oh =>
      match e with
      | Eempty => Ret (oh, tt)
      end.
  
  Definition f x y r: stmt :=
    (#if x
      then (y #= (x - (Int.repr 1)) #;
            r #= (Call "g" [CBV y]) #;
            r #= r + x)
      else (r #= (Int.repr 0))
    ) #;
    Return r.

  Definition g_spec (x: Z) : itree E Z :=
    if negb (x =? 0)%Z
    then
      let y := (x - 1)%Z in
      '(r, _) <- trigger (CallExternal "f" [Vcomp (Vint (Int.repr y))]);;
      match r with
      | Vcomp (Vint i) =>
        let r := (Int.unsigned i) in
        Ret (r + x)%Z
      | _ => triggerUB "asdf"
      end
    else
      Ret 0%Z.

  Definition g_call (args: list val) : itree E (val * list val) :=
    match args with
    | [Vcomp (Vint n)] =>
      res <- g_spec (Int.unsigned n);;
      Ret (Vcomp (Vint (Int.repr res)), args)
    | _ => Ret (Vcomp (Vint (Int.repr 0)), args)
    end.
  
  Definition f_function: function. mk_function_tac f ["x"] ["local0" ; "local1"]. Defined.

  Definition main_program: program := [("main", Rec.main_function)].
  Definition f_program: program := [("f", f_function)].

  Definition g_modsem : ModSem :=
    mk_ModSem
      (fun s => string_dec "g" s)
      _
      (upcast tt)
      EmptyE
      handle_EmptyE
      (fun T (c: CallExternalE T) =>
         let '(CallExternal func_name args) := c in
         if string_dec func_name "g"
         then g_call args
         else triggerUB "ZXCV"
      ).
  
  Definition modsems: list ModSem :=
    g_modsem::(List.map program_to_ModSem [main_program ; f_program]).

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModule.




Module MultiModuleGenv.

  Definition f: stmt :=
    "GVAR1" #= (Int.repr 1000) #;
            Return "GVAR2"
  .

  Definition g: stmt :=
    "GVAR2" #= (Int.repr 2000) #;
            Return "GVAR1"
  .

  Definition main: stmt :=
    (Call "f" []) #;
                  #assume ((Call "g" []) == (Int.repr 1000)) #;
                  #assume ((Call "f" []) == (Int.repr 2000)) #;
                  Put "Test(MultiModuleGenv) passed" Vnull
  .

  Definition main_function: function.
    mk_function_tac main ([]:list var) ([]:list var). Defined.
  Definition f_function: function. mk_function_tac f ([]: list var) ([]: list var). Defined.
  Definition g_function: function. mk_function_tac g ([]: list var) ([]: list var). Defined.

  Definition main_program: program := [("main", main_function)].
  Definition f_program: program := [("f", f_function)].
  Definition g_program: program := [("g", g_function)].

  Definition modsems: list ModSem :=
    List.map program_to_ModSem [main_program ; f_program ; g_program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModuleGenv.





Module MultiModuleLocalState.

  Inductive memoizeE: Type -> Type :=
  | GetM (k: int): memoizeE (option int)
  | SetM (k: int) (v: int): memoizeE unit
  .
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' memoizeE +' GlobalE +' MemoryE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vint k] =>
         v <- trigger (GetM k) ;;
           match v with
           | Some v => triggerSyscall "p" "HIT" [Vnull] ;; Ret (Vcomp (Vint v), [])
           | None => triggerSyscall "p" "MISS" [Vnull] ;;
                                   match (Int.eq k (Int.repr 0)) with
                                   | true => Ret (Vcomp (Vint (Int.repr 0)), [])
                                   | _ => '(prev, _) <- trigger
                                          (CallExternal "g" [Vcomp (Vint (Int.sub k (Int.repr 1)))]);;
                                          match prev with
                                          | Vcomp (Vint prev) =>
                                            let v := (Int.add prev k) in
                                            trigger (SetM k v) ;; Ret (Vcomp (Vint v), [])
                                          | _ => triggerUB "memoizing_f"
                                          end
                                   end
           end
       | _ => triggerUB "memoizing_f"
       end
    )
  .
  Definition f_owned_heap: Type := int -> option int.
  Definition update (oh: f_owned_heap) (k v: int): f_owned_heap :=
    fun x =>
      if Int.eq_dec x k
      then Some v
      else oh x
  .
  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree (GlobalE +' MemoryE +' Event)) :=
    fun T e oh =>
      match e with
      | GetM k => Ret (oh, oh k)
      | SetM k v => Ret (update oh k v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      _
      (fun (_: int) => None: option int)
      memoizeE
      f_handler
      f_sem
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #= (x - (Int.repr 1)) #;
              r #= (Call "f" [CBV y]) #;
              r #= r + x)
      else (r #= (Int.repr 0))
    )
      #;
      Return r
  .
  Definition g_function: function. mk_function_tac g ["x"] ["local0" ; "local1"]. Defined.
  Definition g_program: program := [("g", g_function)].

  Definition main r: stmt :=
    r #= (Call "f" [CBV (Int.repr 10)]) #;
      Put "" r #;

      Put "" (Int.repr 99999) #;
      Put "" (Int.repr 99999) #;
      Put "" (Int.repr 99999) #;

      r #= (Call "f" [CBV (Int.repr 10)]) #;
      Put "" r #;

      Put "" (Int.repr 99999) #;
      Put "" (Int.repr 99999) #;
      Put "" (Int.repr 99999) #;

      r #= (Call "f" [CBV (Int.repr 5)]) #;
      Put "" r #;

      Put "" (Int.repr 99999) #;
      Put "" (Int.repr 99999) #;
      Put "" (Int.repr 99999) #;

      r #= (Call "f" [CBV (Int.repr 8)]) #;
      Put "" r #;

      Skip
  .
  Definition main_function: function.
    mk_function_tac main ([]: list var) ["local0"]. Defined.
  Definition main_program: program := [("main", main_function)].

  Definition modsems: list ModSem :=
    [f_ModSem] ++ List.map program_to_ModSem [main_program ; g_program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModuleLocalState.




Module MultiModuleLocalStateSimple.

  Inductive memoizeE: Type -> Type :=
  | GetM: memoizeE (val)
  | SetM (v: val): memoizeE unit
  .
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' memoizeE +' GlobalE +' MemoryE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vint v] => trigger EYield ;; trigger (SetM v) ;; Ret (Vnull, [])
       | _ => trigger EYield ;; v <-  trigger (GetM) ;; Ret (v, [])
       end)
  .

  Definition f_owned_heap: Type := val.

  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree (GlobalE +' MemoryE +' Event)) :=
    fun T e oh =>
      match e with
      | GetM => Ret (oh, oh)
      | SetM v => Ret (v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      _
      Vnull
      memoizeE
      f_handler
      f_sem
  .

  Definition g: stmt :=
    Return (Int.repr 10)
  .
  Definition g_function: function. mk_function_tac g ([]: list var) ([]: list var). Defined.
  Definition g_program: program := [("g", g_function)].

  Definition main r: stmt :=
    (Call "f" [CBV (Int.repr 10)]) #;
                                   (Call "g" []) #;
                                   Yield #; r #= (Call "f" []) #;
                                   #assume (r == (Int.repr 10)) #;
                                   Debug "passed 1" Vnull #;
                                   (Call "g" []) #;
                                   Yield #; r #= (Call "f" []) #;
                                   #assume (r == (Int.repr 10)) #;
                                   Debug "passed 2" Vnull #;
                                   Yield #; (Call "f" [CBV (Int.repr 20)]) #;
                                   (Call "g" []) #;
                                   Yield #; r #= (Call "f" []) #;
                                   #assume (r == (Int.repr 20)) #;
                                   Debug "passed 3" Vnull #;
                                   Put "Test(MultiModuleLocalStateSimple) passed" Vnull #;
                                   Skip
  .
  Definition main_function: function.
    mk_function_tac main ([]:list var) ["local0"]. Defined.
  Definition main_program: program := [("main", main_function)].

  Definition modsems1: list ModSem :=
    (List.map program_to_ModSem [main_program ; g_program]) ++ [f_ModSem]
  .
  Definition modsems2: list ModSem :=
    [f_ModSem] ++ (List.map program_to_ModSem [main_program ; g_program])
  .

  Definition isem1: itree Event unit := eval_multimodule modsems1.
  Definition isem2: itree Event unit := eval_multimodule modsems2.

End MultiModuleLocalStateSimple.



Module MultiModuleLocalStateSimpleLang.

  Module M1.
    Definition put v: stmt :=
      PutOwnedHeap v
    .
    Definition put_function: function. mk_function_tac put (["v"]: list var) ([]: list var). Defined.

    Definition get: stmt :=
      Return GetOwnedHeap
    .
    Definition get_function: function. mk_function_tac get ([]: list var) ([]: list var). Defined.

    Definition program: program := [("put", put_function) ; ("get", get_function)].
  End M1.

  Module M2.

    Inductive my_type: Type := RED | BLUE.

    Definition check_red: list val -> (val * list val) :=
      (fun v =>
         match v with
         | Vabs a :: _ =>
           match downcast a my_type with
           | Some Red => (Vtrue, nil)
           | _ => (Vfalse, nil)
           end
         | _ => (Vfalse, nil)
         end).

    Definition main r: stmt :=
      (Call "put" [CBV (Int.repr 1)]) #;
      r #= (Call "get" []) #;
      (* Put "r is: " r #; *)
      #assume (r == (Int.repr 1)) #;
      (Call "put" [CBV (Vabs (upcast RED))]) #;
      (* Put "r is: " r #; *)
      r #= (Call "get" []) #;
      #assume (CoqCode [CBV r] check_red) #;
      Skip
    .
    Definition main_function: function. mk_function_tac main ([]: list var) (["r"]: list var). Defined.
    Definition program: program := [("main", main_function)].
  End M2.

  Definition modsems: list ModSem :=
    (List.map program_to_ModSem [M1.program ; M2.program])
  .

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModuleLocalStateSimpleLang.



Module MultiModuleMultiCore.

  Definition producer i: stmt :=
    i #= (Int.repr 10) #;
      #while i
      do (
        Debug "PRODUCER: " i #;
              #if "GVAR" == (Int.repr 0)
               then ("GVAR" #= i #; i #= i - (Int.repr 1))
               else Skip #;
                         Yield
      ) #;
      "SIGNAL" #= "SIGNAL" + (Int.repr 1)
  .

  Definition consumer s: stmt :=
    s #= (Int.repr 0) #;
      #while true
      do (
        Debug "CONSUMER: " s #;
              #if "GVAR" == (Int.repr 0)
               then Skip
               else s #= s + "GVAR" #;
                                    "GVAR" #= (Int.repr 0)
                                    #;
                                    #if "SIGNAL" == (Int.repr 2) then Break else Skip #;
                                                                                      Yield
      ) #;
      (* Put "" s #; *)
      #assume (s == (Int.repr 110)) #;
      Put "Test(MultiCore3) passed" Vnull
  .

  Definition producerF: function. mk_function_tac producer ([]: list var) (["i"]). Defined.
  Definition consumerF: function. mk_function_tac consumer ([]: list var) (["s"]). Defined.

  Definition producerP: program := [("producer", producerF) ].
  Definition consumerP: program := [("consumer", consumerF) ].

  Definition programs: list program := [ producerP ; consumerP ].
  Definition modsems: list ModSem := List.map program_to_ModSem programs.

  Definition sem: itree Event unit :=
    eval_multimodule_multicore modsems [ "producer" ; "producer" ; "consumer" ].

End MultiModuleMultiCore.


Module MultiModuleMultiCoreLocalState.

  Inductive memoizeE: Type -> Type :=
  | GetM: memoizeE (val)
  | SetM (v: val): memoizeE unit
  .
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' memoizeE +' GlobalE +' MemoryE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vint v] => trigger EYield ;; trigger (SetM v) ;; Ret (Vnull, [])
       | _ => trigger EYield ;; v <-  trigger (GetM) ;; Ret (v, [])
       end)
  .

  Definition f_owned_heap: Type := val.

  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree (GlobalE +' MemoryE +' Event)) :=
    fun T e oh =>
      match e with
      | GetM => Ret (oh, oh)
      | SetM v => Ret (v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      _
      Vnull
      memoizeE
      f_handler
      f_sem
  .

  Definition setter: stmt :=
    (Call "f" [CBV (Int.repr 10)]) #;
                                   "SIGNAL" #= (Int.repr 1) #;
                                   Skip
  .

  Definition getter: stmt :=
    #while "SIGNAL" == (Int.repr 0) do Yield #;
                                    #assume ((Call "f" []) == (Int.repr 10)) #;
                                    Put "Test(MultiModuleMultiCoreLocalState) passed" Vnull #;
                                    Skip
  .

  Definition setterF: function.
    mk_function_tac setter ([]:list var) ([]:list var). Defined.
  Definition setterP: program := [("setter", setterF)].

  Definition getterF: function.
    mk_function_tac getter ([]:list var) ([]:list var). Defined.
  Definition getterP: program := [("getter", getterF)].

  Definition modsems: list ModSem :=
    (List.map program_to_ModSem [setterP ; getterP]) ++ [f_ModSem]
  .

  Definition isem: itree Event unit :=
    eval_multimodule_multicore modsems ["setter" ; "getter"].

End MultiModuleMultiCoreLocalState.


Module PrintAny.

  Inductive my_type: Type := RED | BLUE.
  Instance my_type_Showable: Showable my_type := { show := fun x => match x with | RED => "RED" | BLUE => "BLUE" end }.

    Definition main: stmt :=
      Put "Red is: " (Vabs (upcast RED)) #;
      Put "Blue is: " (Vabs (upcast BLUE)) #;
      Put "Test(PrintAny) passed" Vnull #;
      Skip
    .
    Definition main_function: function. mk_function_tac main ([]: list var) ([]: list var). Defined.
    Definition program: program := [("main", main_function)].

  Definition modsems: list ModSem :=
    (List.map program_to_ModSem [program])
  .

  Definition isem: itree Event unit := eval_multimodule modsems.

End PrintAny.


Module PrintTest.

  Require Import BinaryString.

  Include Raw.
  Definition string_gen (n: N): string :=
    of_N n.

  From Coq Require Import
       ZArith
       ZArith.Znat.

  Definition z_gen (n: N) : Z :=
    Z.of_N n.


  Definition Z_to_string_gen (n : Z) : string :=
    of_Z n.
  
End PrintTest.


Module HexPrintTest.

  Require Import HexString.

  Include Raw.
  Definition string_gen (n: N): string :=
    of_N n.

  From Coq Require Import
       ZArith
       ZArith.Znat.

  Definition z_gen (n: N) : Z :=
    Z.of_N n.


  Definition Z_to_string_gen (n : Z) : string :=
    of_Z n.
  
End HexPrintTest.
