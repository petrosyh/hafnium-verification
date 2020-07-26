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
Require Import Coqlib sflib.


(* From HafniumCore *)
Require Import TestAux.
Require Import Lang.
Require Import Types.
Require Import ADDR.

Import LangNotations.


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.

Module TEST1.
  Include ADDR.
  
  Definition main v pa v2 ipa v3 v4 ipa2 pa2 v5 va ptr va2 v6: stmt :=
    v #= Vnat 42#;
      pa #= (Call "pa_init" [CBV v]) #;
      v2 #= (Call "pa_addr" [CBV pa]) #;
      #assume (v2 == v) #;
      ipa #= (Call "ipa_from_pa" [CBV pa]) #;
      v3 #= (Call "ipa_addr" [CBV ipa]) #;
      #assume (v3 == v) #;
      v4 #= Vnat 18#;
      ipa2 #= (Call "ipa_add" [CBV ipa; CBV v4]) #;
      pa2 #= (Call "pa_from_ipa" [CBV ipa2]) #;
      v5 #= (Call "pa_difference" [CBV pa; CBV pa2]) #;
      #assume (v5 == v4) #;
      va #= (Call "va_init" [CBV v4]) #;
      ptr #= (Call "ptr_from_va" [CBV va]) #;
      va2 #= (Call "va_from_ptr" [CBV ptr]) #;
      v6 #= (Call "va_addr" [CBV va2]) #;
      #assume (v6 == v4) #;
      Put "Test(ADDR) passed" Vnull
  .

  Definition main_function: function.
    mk_function_tac main ([]:list var)
                    ["v"; "pa"; "v2"; "ipa"; "v3"; "v4"; "ipa2";
                     "pa2"; "v5"; "va"; "ptr"; "va2"; "v6"].
  Defined.
  
  Definition program: program :=
    [
      ("pa_init", pa_initF) ;
        ("pa_addr", pa_addrF) ;
        ("pa_add", pa_addF) ;
        ("pa_difference", pa_differenceF) ;
        ("ipa_init", ipa_initF) ;
        ("ipa_addr", ipa_addrF) ;
        ("ipa_add", ipa_addF) ;
        ("va_init", va_initF) ;
        ("va_addr", va_addrF) ;
        ("va_from_pa", va_from_paF) ;
        ("ipa_from_pa", ipa_from_paF) ;
        ("pa_from_va", pa_from_vaF) ;
        ("pa_from_ipa", pa_from_ipaF) ;
        ("va_from_ptr", va_from_ptrF) ;
        ("ptr_from_va", ptr_from_vaF) ;
        ("main", main_function)
    ].

  Definition modsems: list ModSem :=
    List.map program_to_ModSem [program].

  Definition isem: itree Event unit := eval_multimodule modsems.
  
End TEST1.
