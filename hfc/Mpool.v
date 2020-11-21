(*
 * Copyright 2020 Youngju Song/ Jieung Kim
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
Require Import Lang.
Require Import Values.
Require Import Integers.
Require Import Constant.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

(* XXX: Need to move this part into Lang.v file *)
(* Section STORELOADSYNTACTICSUGAR. *)

(*   (* The following two accessors for debugging *) *)

(*   Definition store_at_i (p : var) (offset : Int64.int) (e: expr) : stmt := *)
(*     ((Cast (Plus (Cast p tint) (offset * (Int64.repr 8))) tptr) @ Int64.zero #:= e). *)
  
(*   Definition load_at_i (p : var) (offset : Int64.int) : expr := *)
(*     (Cast (Plus (Cast p tint) (offset * (Int64.repr 8))) tptr) #@ Int64.zero.   *)
  
(*   (* The following two accessors for debugging *) *)
(*   Definition debug_1 := "debug1". *)
(*   Definition debug_2 := "debug2". *)
(*   Definition debug_3 := "debug3". *)

(*   Definition store_and_load_at_i_debug  (p : var) (offset : Int64.int) : stmt :=  *)
(*     debug_1 #=  (Cast p tint) #; *)
(*             Put "accessor_debug: debug_1" debug_1 #; *)
(*             debug_2 #= (offset * (Int64.repr 8)%Z) #; *)
(*             Put "accessor_debug: debug_2" debug_2 #; *)
(*             debug_3 #= (debug_1 + debug_2) #; *)
(*             Put "accessor_debug: debug_3" debug_3 #; *)
(*             Put "accessor_debug: debug_3 ptr" (Cast debug_3 tptr). *)
  
(* End STORELOADSYNTACTICSUGAR. *)
  
Module MPOOLCONCURSTRUCT.

  (************************************************)
  (*                 Structures                   *)
  (************************************************)
  (*
  struct mpool_chunk {
 	struct mpool_chunk *next_chunk;
	struct mpool_chunk *limit;
  };
   *)
  
  Definition next_chunk_loc := Int64.repr 0%Z.
  Definition limit_loc := Int64.repr 1%Z.

  (*
  struct mpool_entry {
	struct mpool_entry *next;
  };  
  *)

  Definition next_loc := Int64.repr 0%Z.
  
  (*
  struct mpool {
	struct spinlock lock;
	size_t entry_size;
	struct mpool_chunk *chunk_list;
	struct mpool_entry *entry_list;
	struct mpool *fallback;
  };
  *)

  Definition lock_loc := Int64.repr 0%Z.
  Definition entry_size_loc := Int64.repr 1%Z.
  Definition chunk_list_loc := Int64.repr 2%Z.
  Definition entry_list_loc := Int64.repr 3%Z.
  Definition fallback_loc := Int64.repr 4%Z.

End MPOOLCONCURSTRUCT.

Module MPOOLCONCUR.

  Import MPOOLCONCURSTRUCT.
  Import LangNotations.

  (************************************************)
  (*             Global variable                  *)
  (************************************************)

  Definition mpool_locks_enabled := "mpool_locks_enabled".

  (************************************************)
  (*           Mpool lock functions               *)
  (************************************************)
  
  (* No matching function, but it has to be used in the test cases *)
  Definition mpool_init_locks :=
    mpool_locks_enabled #= Vfalse.
  
  (* 
  void mpool_enable_locks(void)
  {
	mpool_locks_enabled = true;
  } 
  *)

  Definition mpool_enable_locks :=
    mpool_locks_enabled  #= Vtrue.

  (*
  static void mpool_lock(struct mpool *p)
  {
	if (mpool_locks_enabled) {
		sl_lock(&p->lock);
	}
  }
  *)
  
  Definition mpool_lock (p : var) :=
    (* Debugging messages *)
    (* (Put "mpool_lock: start" (p #@ lock_loc)) 
      #; *)
    #if mpool_locks_enabled
     then (Call "Lock.acquire" [CBV (p #@ lock_loc) ; CBV p])
     else Skip.
  
  (*
  static void mpool_unlock(struct mpool *p)
  {
	if (mpool_locks_enabled) {
		sl_unlock(&p->lock);
	}
  }
  *)
  
  Definition mpool_unlock (p : var) :=
    (* Debugging messages *)
    (* (Put "mpool_lock: start" (p #@ lock_loc)) 
      #; *)
    #if mpool_locks_enabled
     then (Call "Lock.release" [CBV (p #@ lock_loc) ; CBV p])
     else Skip.

  (************************************************)
  (*           Mpool init functions               *)
  (************************************************)
  
  (*
  void mpool_init(struct mpool *p, size_t entry_size)
  {
	p->entry_size = entry_size;
	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;
	sl_init(&p->lock);
  }
  *)
  
  Definition mpool_init (p:var) (entry_size : var): stmt :=
    Put "mpool_init: start" p #;
        p @ entry_size_loc #:= entry_size #;
        p @ chunk_list_loc #:= Vnull #;
        p @ entry_list_loc #:= Vnull #;
        p @ fallback_loc #:= Vnull #;
        p @ lock_loc #:= (Call "Lock.new" []) #;
        (Call "MPOOL.mpool_unlock" [CBR p]) #;
        Put "mpool init: end" p.

  (*
  void mpool_init_from(struct mpool *p, struct mpool *from)
  {
	mpool_init(p, from->entry_size);

	mpool_lock(from);
	p->chunk_list = from->chunk_list;
	p->entry_list = from->entry_list;
	p->fallback = from->fallback;

	from->chunk_list = NULL;
	from->entry_list = NULL;
	from->fallback = NULL;
	mpool_unlock(from);
  }
  *)

  Definition mpool_init_from (p from: var) : stmt :=
    Put "mpool_init_from: start" p #;    
        (Call "MPOOL.mpool_init" [CBR p; CBV (from #@ entry_size_loc)]) #;
        (Call "MPOOL.mpool_lock" [CBR from]) #; 
        p @ chunk_list_loc #:= (from #@ chunk_list_loc) #;
        p @ entry_list_loc #:= (from #@ entry_list_loc) #;
        p @ fallback_loc #:= (from #@ fallback_loc) #;
        from @ chunk_list_loc #:= Vnull #;
        from @ entry_list_loc #:= Vnull #;
        from @ fallback_loc #:= Vnull #;
        (Call "MPOOL.mpool_unlock" [CBR from]) #;
        Put "mpool_init_from: end" p. 
      
  (*
  void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback)
  {
	mpool_init(p, fallback->entry_size);
	p->fallback = fallback;
  }
  *)

  Definition mpool_init_with_fallback (p fallback: var) : stmt :=
    Put "mpool_init_with_fallback: start" p #;        
        Call "MPOOL.mpool_init" [CBR p; CBV (fallback #@ entry_size_loc)] #;
        p @ fallback_loc #:= fallback #;
        Put "mpool_init_with_fallback: end" p.

  (************************************************)
  (*                 Mpool fini                   *)
  (************************************************)
    
  (*
  void mpool_fini(struct mpool *p)
  {
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

	if (!p->fallback) {
		return;
	}

	mpool_lock(p);

	/* Merge the freelist into the fallback. */
	entry = p->entry_list;
	while (entry != NULL) {
		void *ptr = entry;

		entry = entry->next;
		mpool_free(p->fallback, ptr);
	}

	/* Merge the chunk list into the fallback. */
	chunk = p->chunk_list;
	while (chunk != NULL) {
		void *ptr = chunk;
		size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk;

		chunk = chunk->next_chunk;
		mpool_add_chunk(p->fallback, ptr, size);
	}

	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;

	mpool_unlock(p);
  }
  *)
  
  Definition mpool_fini (p : var) (entry chunk ptr size: var) : stmt :=
    Put "mpool_fini: start" p #;
    (Call "MPOOL.mpool_lock" [CBR p]) #;
    entry #= (p #@ entry_list_loc) #;
    Put "entry : " entry #;
    #while (#! (entry == Vnull))  
    do (
        Put "debug0 : " Vnull #;
        ptr #= entry #;
            entry #= (entry #@ next_loc) #;
            (Call "MPOOL.mpool_free" [CBV (p #@ fallback_loc); CBR ptr])
      ) #;
        chunk #= (p #@ chunk_list_loc) #;
        Put "chunk : " chunk #;
        #while (#! (chunk == Vnull))
        do (
            Put "debug1 : " Vnull #;
            Put "mpool_fini: chunk that will be added" chunk #;
            ptr #= chunk #;
                size #= ((Cast (chunk #@ limit_loc) tint) - (Cast chunk tint))
                #;
                chunk #= (chunk #@ next_chunk_loc) #;
                (Call "MPOOL.mpool_add_chunk" [CBV (p #@ fallback_loc); CBR ptr; CBV size]) #;
                (* add the following two lines for debugging *)
                ptr #= (p #@ fallback_loc) #; 
                Put "mpool_fini: chunk that is added"
                (ptr #@ next_chunk_loc)
          ) #;
            p @ chunk_list_loc #:= Vnull #;
            p @ entry_list_loc #:= Vnull #;
            p @ fallback_loc #:= Vnull #;            
            (Call "MPOOL.mpool_unlock" [CBR p]) #;
            Put "mpool_fini: end" p.

  (************************************************)
  (*              Mpool add chunk                 *)
  (************************************************)

  (*
  bool mpool_add_chunk(struct mpool *p, void *begin, size_t size)
  {
	struct mpool_chunk *chunk;
	uintptr_t new_begin;
	uintptr_t new_end;

	new_begin = ((uintptr_t)begin + p->entry_size - 1) / p->entry_size *
		    p->entry_size;
	new_end = ((uintptr_t)begin + size) / p->entry_size * p->entry_size;

	if (new_begin >= new_end || new_end - new_begin < p->entry_size) {
		return false;
	}

	chunk = (struct mpool_chunk * )new_begin;
	chunk->limit = (struct mpool_chunk * )new_end;

	mpool_lock(p);
	chunk->next_chunk = p->chunk_list;
	p->chunk_list = chunk;
	mpool_unlock(p);

	return true;
  }
  *)

  Definition mpool_add_chunk (p begin size : var) (new_begin new_end chunk temp: var) : stmt :=
    Put "mpool_add_chunk: start" p #;
        (* Put "mpool_add_chunk: (p #@ entry_size_loc)" (p #@ entry_size_loc) #; *)
        new_begin #= (((Cast begin tint) + (p #@ entry_size_loc) - (Int64.repr 1))
                        / (p #@ entry_size_loc) * (p #@ entry_size_loc))
        #;
        Put "mpool add chunk debug0" Vnull #;
        new_end #= (((Cast begin tint) + size)
                      / (p #@ entry_size_loc) * (p #@ entry_size_loc)) #;
        Put "mpool add chunk debug1" Vnull #;
        
        (* Debugging messages *)
        (*
        Put "mpool_add_chunk: new_begin" new_begin #;
        Put "mpool_add_chunk: new_end" new_end #;
        Put "mpool_add_chunk: value_at_limit_loc" (p #@ limit_loc) #;
        Put "mpool_add_chunk: condition1" (new_end <= new_begin) #;
        Put "mpool_add_chunk: condition2" ((new_end - new_begin) < (p #@ entry_size_loc)) #;
        Put "mpool_add_chunk: value_at_limit" (p #@ limit_loc) #;
        Put "mpool_add_chunk: value_at_entry_size_loc" (p #@ entry_size_loc) #;
        Put "mpool_add_chunk: value_at_chunk_list" (p #@ chunk_list_loc) #;
        Put "mpool_add_chunk: value_at_entry_list" (p #@ entry_list_loc) #;
        Put "mpool_add_chunk: value_at_fallback_loc" (p #@ fallback_loc) #; *)
        ((new_end <= new_begin) #|| ((new_end - new_begin) < (p #@ entry_size_loc))) #;
        (#if (((new_end <= new_begin) #|| ((new_end - new_begin) < (p #@ entry_size_loc))))
          then
            Put "mpool_add_chunk: failed" p #;
            Return Vfalse
          else
            chunk #= (Cast new_begin tptr) #;
                  (chunk @ limit_loc #:= (Cast new_end tptr)) #;              
                  (Call "MPOOL.mpool_lock" [CBR p]) #;
                  (chunk @ next_chunk_loc #:= (p #@ chunk_list_loc)) #;
                  (p @ chunk_list_loc #:= chunk) #;              
                  (Call "MPOOL.mpool_unlock" [CBR p]) #;
                  (* Debugging messages *)
                  (*
                  Put "mpool_add_chunk: value_at_limit" (p #@ limit_loc) #;
                  Put "mpool_add_chunk: (p #@ entry_size_loc)" (p #@ entry_size_loc) #;
                  Put "mpool_add_chunk: (p #@ entry_list)" (p #@ entry_list_loc) #;
                  Put "mpool_add_chunk: (p #@ fallback_loc)" (p #@ fallback_loc) #; *)
                  Put "mpool_add_chunk: the first chunk list loc (p #@ chunk_list)"
                  (p #@ chunk_list_loc) #;
                  Put "mpool_add_chunk: the first chunk loc (chunk)" chunk #; 
                  Put "mpool_add_chunk: the second chunk loc (chunk #@ next_chunk_loc)"
                  (chunk #@ next_chunk_loc) #;
                  Put "mpool_add_chunk: the first chunk's limit (chunk #@ limit)"
                  (chunk #@ limit_loc) #;
                  Put "mpool_add_chunk: finish" p #; 
                  Return Vtrue).

  (************************************************)
  (*                Mpool free                    *)
  (************************************************)
   
  (*
  void mpool_free(struct mpool *p, void *ptr)
  {
	struct mpool_entry *e = ptr;

	/* Store the newly freed entry in the front of the free list. */
	mpool_lock(p);
	e->next = p->entry_list;
	p->entry_list = e;
	mpool_unlock(p);
  }
  *)
  
  Definition mpool_free (p ptr : var) (e: var):=
    Put "mpool_free: start" p #;
        (* Debugging messages *)
        Put "mpool_free: it will free this one" ptr #;
        e #= ptr #;
        (Call "MPOOL.mpool_lock" [CBR p]) #; 
        (e @ next_loc #:= (p #@ entry_list_loc)) #;
        (p @ entry_list_loc #:= e) #;
        (Call "MPOOL.mpool_unlock" [CBR p]) #;
        Put "mpool_free: end" p #;
        Skip.

  (************************************************)
  (*                Mpool alloc                   *)
  (************************************************)
  
  (* Instead of defining [mpool_alloc] and [mpool_alloc_contiguous], 
     I only define [mpool_alloc_contiguous] because it is possible for us to use 
     [mpool_alloc_contiguous] for both purposes *)

  (*
  void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count,
    					 size_t align)
  {
	struct mpool_chunk **prev;
	void *ret = NULL;

	align *= p->entry_size;

	mpool_lock(p);


	prev = &p->chunk_list;
	while ( *prev != NULL) {
		uintptr_t start;
		struct mpool_chunk *new_chunk;
		struct mpool_chunk *chunk = *prev;

		start = (((uintptr_t)chunk + align - 1) / align) * align;


		new_chunk =
			(struct mpool_chunk * )(start + (count * p->entry_size));
		if (new_chunk <= chunk->limit) {
			if (new_chunk == chunk->limit) {
				*prev = chunk->next_chunk;
			} else {
				*new_chunk = *chunk;
				*prev = new_chunk;
			}



			if (start - (uintptr_t)chunk >= p->entry_size) {
				chunk->next_chunk = *prev;
				*prev = chunk;
				chunk->limit = (struct mpool_chunk * )start;
			}

			ret = (void * )start;
			break;
		}

		prev = &chunk->next_chunk;
	}

	mpool_unlock(p);

	return ret;
  }
  *)

  (* XXX: This version is a really simplified version to make it work first. we have to 
          replace this version after we properly modify the original version above *)  
  Definition mpool_alloc_contiguous_no_fallback
             (p count align: var)
             (prev prev_cast ret chunk start new_chunk temp: var): stmt :=
    (Put "mpool_alloc_contiguous_no_fallback: start" p) #;
    ret #= Vnull #;
    align #= (align * (p #@ entry_size_loc))
    #;
    (Call "MPOOL.mpool_lock" [CBR p]) #;
    
    prev #= ((Cast p tint) + (chunk_list_loc * (Int64.repr 8))) #;
    (* simplified version - we will not add "start - (uintptr_t)chunk >= p->entry_size" 
       even though we have the remaining chunk at the beginning *)
    prev_cast #= (Cast prev tptr) #;
    (* Debugging messages: *)
    (*
    Put "mpool_alloc_contiguous_no_fallback: prev address: " prev #;
    Put "mpool_alloc_contiguous_no_fallback: value in the prev: " (prev_cast #@ (Int64.repr 0)) #; *)
    Put "checker : " (prev_cast #@ (Int64.repr 0)) #;
    #while (#! ((prev_cast #@ (Int64.repr 0)) == Vnull))
    do (
        chunk #= (prev_cast #@ (Int64.repr 0)) #;
              start #= ((((Cast chunk tint) + align - (Int64.repr 1)) / align) * align)
              #;
              new_chunk #= (Cast (start + (count * (p #@ entry_size_loc))) tptr) #;
              (* Debugging messages: *)
              (*
              Put "mpool_alloc_contiguous_no_fallback: chunk: " chunk #;
              Put "mpool_alloc_contiguous_no_fallback: start: " start #;
              Put "mpool_alloc_contiguous_no_fallback: new_chunk: " (Cast new_chunk tint) #;
              Put "mpool_alloc_contiguous_no_fallback: first cond: " *)
              ((Cast new_chunk tint) <= (Cast (chunk #@ limit_loc) tint)) #; 
              (#if ((Cast new_chunk tint) <= (Cast (chunk #@ limit_loc) tint))
                then
                  (* Debugging messages: *)
                  (* 
                  Put "mpool_alloc_contiguous_no_fallback: alloc is available" start #; *)
                  (#if ((Cast new_chunk tint) == (Cast (chunk #@ limit_loc) tint))
                    then (prev_cast @ (Int64.repr 0) #:= (chunk #@ next_chunk_loc))
                    else
                      (new_chunk @ limit_loc #:= (chunk #@ limit_loc)) #;
                      (new_chunk @ next_chunk_loc #:= (chunk #@ next_chunk_loc)) #; 
                      (prev_cast @ (Int64.repr 0) #:= new_chunk))
                    #;
                    ret #= (Cast start tptr) #;
                    Put "RET: " ret #;
                    Break 
                else
                  prev #= ((Cast chunk tint) +
                           (next_chunk_loc * (Int64.repr 8))) #;
                       prev_cast #= (Cast prev tptr) 
                       (* Debugging messages: *)
                       (*
                       #;
                       Put "mpool_alloc_contiguous_no_fallback: prev address: " prev #;
                       Put "mpool_alloc_contiguous_no_fallback: value in the prev: " (prev_cast #@ (Int64.repr 0)) 
                       *)
              ) 
      ) #;
        (Call "MPOOL.mpool_unlock" [CBR p]) #;
        Put "RET final: " ret #;
        Return ret.

  (* XXX: The following version is a naively translated version, but it has an error.

     It has a problem with pointer alaising, so it cannot update the values in the p after
     it allocate a new memory (It cannot update the previous chunk information). 
     We have to rewrite programs when we have pointer alaising in it. *)
  (*
  Definition mpool_alloc_contiguous_no_fallback
             (p count align: var)
             (prev_address prev ret chunk start new_chunk temp: var): stmt :=
    ret #= Vnull #;
    align #= (align * (p #@ entry_size_loc))
    #;
    (Call "MPOOL.mpool_lock" [CBR p]) #;
    prev #= (p #@ chunk_list_loc) #;
    #while (#! (prev == Vnull))
    do (
        chunk #= prev #;
              start #= ((((Cast chunk tint) + align - (Int64.repr 1)) / align) * align)
              #;
              new_chunk #= (Cast (start + (count * (p #@ entry_size_loc))) tptr) #;
              Put "mpool_alloc_contiguous_no_fallback: start" start #;
              Put "mpool_alloc_contiguous_no_fallback: new_chunk" new_chunk #;
              (#if ((Cast new_chunk tint) <= (Cast (chunk #@ limit_loc) tint))
                then (#if ((Cast new_chunk tint) == (Cast (chunk #@ limit_loc) tint))
                       then
                         prev #= (chunk #@ next_chunk_loc)
                       else new_chunk #= chunk #;
                            prev #= new_chunk)
                       #;
                       (#if ((p #@ entry_size_loc) <= start - (Cast chunk tint))
                         then (chunk @ next_chunk_loc #:= prev)
                                #;
                                prev #= chunk #; 
                                (chunk @ limit_loc #:= (Cast start tptr))
                         else Skip) #;
                       ret #= (Cast start tptr) #;
                       Break
                else Skip) #;
              prev #= (chunk #@ next_chunk_loc)
      ) #;
        (Call "MPOOL.mpool_unlock" [CBR p]) #;
        (prev @ (Int64.repr 0) #:= (chunk #@ next_chunk_loc)) #;
        Return ret.
   *)
  
  

  (*
  void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align)
  {
	do {
		void *ret = mpool_alloc_contiguous_no_fallback(p, count, align);

		if (ret != NULL) {
			return ret;
		}

		p = p->fallback;
	} while (p != NULL);

	return NULL;
  }
  *)  

   Definition mpool_alloc_contiguous (p count align: var) (ret : var) : stmt :=
    Put "mpool_alloc_contiguous: start" p #;            
    #while Vtrue
     do (
         (* Debugging messages *)
         (*
         Put "mpool_alloc_contiguous: looping mpool_alloc_contiguous" p #; 
             Put "while loop in the mpool_alloc" p #; *)
         ret #= (Call "MPOOL.mpool_alloc_contiguous_no_fallback" [CBR p ; CBV count; CBV align]) #;
             (* Debugging messages *)
             (*
             Put "mpool_alloc_contiguous: looping mpool_alloc_contiguous_no_fallback" ret #; *)
             Put "ret before : " ret #;
             (#if (ret)
               then
                 (* Debugging messages *)
                 (* Put "mpool_alloc_contiguous: end" ret #; *)
                 Break
               else Skip) #;
             Put "fallback" (p #@ fallback_loc) #;
             p #= (p #@ fallback_loc)
             #;
             #if (p)
              then Skip
              else Break
       ) #;
         Put "mpool_alloc_contiguous: end" ret #;         
         Return ret.

  (* XXX: The following version is a naively translated version, but it has an error.
     It will always return the null value as its result 

     This one raises an error because of Return statement in the middle of while body. 
     It seesm when we call this funciton, it will always walk until the end of 
     the function (even though we have Return in the middle) 
     and return Vnull as its result. Therefore, when we call it in our test cases, 
     it will always return 0 for the ret and p will become 0 when we call it via call by reference *)
  (*
  Definition mpool_alloc_contiguous (p count align: var) (ret : var) : stmt :=
    Put "mpool_alloc_contiguous: start" p #;            
    #while Vtrue
     do (
         ret #= (Call "MPOOL.mpool_alloc_contiguous_no_fallback" [CBR p ; CBV count; CBV align]) #;
         (#if (ret)
           then Return ret 
           else Skip) #;
         p #= (p #@ fallback_loc)
         #;
         #if (p)
          then Skip
          else Break
       ) #;
         Return Vnull.
   *)

  (* Function definitions *)
  Definition mpool_init_locksF: function.
    mk_function_tac mpool_init_locks ([]: list var) ([]: list var).
  Defined.
  Definition mpool_enable_locksF: function.
    mk_function_tac mpool_enable_locks ([]: list var) ([]: list var).
  Defined.
  Definition mpool_lockF: function.
    mk_function_tac mpool_lock ["p"] ([]: list var).
  Defined. 
  Definition mpool_unlockF: function.
    mk_function_tac mpool_unlock ["p"] ([]: list var).
  Defined.
  Definition mpool_initF: function.
    mk_function_tac mpool_init ["p"; "entry_size"] ([]: list var).
  Defined.
  Definition mpool_init_fromF: function.
    mk_function_tac mpool_init_from ["p"; "from"] ([]: list var).
  Defined.
  Definition mpool_init_with_fallbackF: function.
    mk_function_tac mpool_init_with_fallback ["p"; "fallback"] ([]: list var).
  Defined.
  Definition mpool_finiF: function.
    mk_function_tac mpool_fini ["p"] ["entry"; "chunk"; "ptr"; "size"].
  Defined.
  Definition mpool_add_chunkF: function.
    mk_function_tac mpool_add_chunk ["p"; "begin"; "size"] ["new_begin"; "new_end"; "chunk"; "temp"].
  Defined.
  Definition mpool_freeF: function.
    mk_function_tac mpool_free ["p"; "ptr"] ["e"].
  Defined.
  Definition mpool_alloc_contiguous_no_fallbackF: function.
    mk_function_tac mpool_alloc_contiguous_no_fallback ["p"; "count"; "align"]
                    [ "prev"; "prev_cast"; "ret"; "chunk"; "start"; "new_chunk"; "temp"].
  Defined.
  Definition mpool_alloc_contiguousF: function.
    mk_function_tac mpool_alloc_contiguous ["p"; "count"; "align"] ["ret"].
  Defined.


  (* For debugging *)
  Definition print_mpool (p chunk entry i:var) : stmt :=
    Put "------------print mpool------------" (Vabs (Any.upcast tt)) #;
    Put "mpool pointer:" p #;
    Put "entry_size:" (p #@ entry_size_loc) #;
    chunk #= (p #@ chunk_list_loc) #;
    i #= (Int.repr 0) #;
    (#while chunk
      do
      (Put "  chunk" i #;
           Put "    start:" chunk #;
           Put "    end:" (chunk #@ limit_loc) #;
           Put "    size:" ((Cast (chunk #@ limit_loc) tint) - (Cast chunk tint)) #;
           chunk #= (chunk #@ next_chunk_loc) #;
           i #= i + (Int.repr 1)))
    #;
    entry #= (p #@ entry_list_loc) #;
    i #= (Int.repr 0) #;
    (#while entry
      do
      (Put "  entry " i #;
           Put "    " entry #;
           entry #= (entry #@ next_loc) #;
           i #= i + (Int.repr 1)))
    #;
    Put "fallback:" (p #@ fallback_loc).
  
  Definition print_mpoolF: function.
    mk_function_tac print_mpool ["p"] ["chunk"; "entry"; "i"].
  Defined.

  (* MPOOL module definition *)
  Definition mpool_program: program :=
      [
        ("MPOOL.mpool_init_locks", mpool_init_locksF) ;
      ("MPOOL.mpool_enable_locks", mpool_enable_locksF) ;
      ("MPOOL.mpool_lock", mpool_lockF) ;
      ("MPOOL.mpool_unlock", mpool_unlockF) ;
      ("MPOOL.mpool_init", mpool_initF) ;
      ("MPOOL.mpool_init_from", mpool_init_fromF) ;
      ("MPOOL.mpool_init_with_fallback", mpool_init_with_fallbackF) ;
      ("MPOOL.mpool_fini", mpool_finiF) ;
      ("MPOOL.mpool_add_chunk", mpool_add_chunkF) ;
      ("MPOOL.mpool_free", mpool_freeF) ;
      ("MPOOL.mpool_alloc_contiguous_no_fallback", mpool_alloc_contiguous_no_fallbackF) ;
      ("MPOOL.mpool_alloc_contiguous", mpool_alloc_contiguousF);
      ("MPOOL.print_mpool", print_mpoolF)
      ].
  
  Definition mpool_modsem : ModSem := program_to_ModSem mpool_program.
    
End MPOOLCONCUR.

Require Import Maps.
Set Implicit Arguments.

Section ABSTSTATE.

Variable A: Type.
Definition chunk : Type := list A.
Definition entry : Type := list A.
    
Inductive Mpool : Type :=
  mkMpool {
      entry_size : Z;
      chunk_list : list chunk;
      entry_list : list entry;
      fallback: option positive
    }.

Record MpoolAbstState : Type :=
  mkMpoolAbstState {
      mpool_map : PMap.t Mpool; (* id -> mpool *)
      addr_to_id : ZMap.t positive; (* mem addr -> id *)
      next_id : positive; (* new mpool id *)
    }.

End ABSTSTATE.

Section HIGHSPEC.

Variable A: Type.
Variable st: MpoolAbstState A.

Definition mpool_init_spec (p entry_size:Z) : MpoolAbstState A :=
  let mp := mkMpool entry_size [] [] None in
  let i := next_id st in
  mkMpoolAbstState (PMap.set i mp (mpool_map st)) (ZMap.set p i (addr_to_id st)) (Pos.succ i).
                    
Definition mpool_free_spec (p:Z) (ptr:list A) :=
  let i := ZMap.get p (addr_to_id st) in
  let mp := (mpool_map st) !! i in
  let mp' := mkMpool (entry_size mp) (chunk_list mp) (ptr::entry_list mp) (fallback mp) in
  mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i.

Definition mpool_add_chunk_spec (p:Z) (c:chunk A) (size:Z) :=
  let i := ZMap.get p (addr_to_id st) in
  let mp := (mpool_map st) !! i in
  let mp' := mkMpool (entry_size mp) (c::(chunk_list mp)) (entry_list mp) (fallback mp) in
  (mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i, true).

Definition mpool_alloc_no_fallback_spec (p:Z) :=
  let i := ZMap.get p (addr_to_id st) in
  let mp := (mpool_map st) !! i in
  let entry := (entry_list mp) in
  if negb (Nat.eqb (length entry) O)
  then (
      let mp' := mkMpool (entry_size mp) (chunk_list mp) (tl (entry_list mp)) (fallback mp) in
      (mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i, Some (hd entry))
    )
  else
    (
      let chunk := (chunk_list mp) in
      if (Nat.eqb (length chunk) O)
      then (st, None)
      else
    (* should handle ugly case *)
      let mp' := mkMpool (entry_size mp) (tl (chunk_list mp)) (entry_list mp) (fallback mp) in
      ((mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i), (Some (hd chunk)))
    ).
    
End HIGHSPEC.

Section ALLOC.

Context {iteration_bound: nat}.
Variable A: Type.
Hypothesis id_to_addr : positive -> Z.

Fixpoint mpool_alloc_spec_aux (st:MpoolAbstState A) (p:Z) (n:nat) :=
  match n with
  | O => (st, None)
  | S n' =>
    let i := ZMap.get p (addr_to_id st) in
    let mp := (mpool_map st) !! i in
    let (st', ret) := mpool_alloc_no_fallback_spec st p in
    match ret with
    | Some ret => (st', Some ret)
    | None => match (fallback mp) with
             | None => (st', None)
             | Some mp' => mpool_alloc_spec_aux st' (id_to_addr mp') n'
             end
    end
  end.

Definition mpool_alloc_spec (st:MpoolAbstState A) (p:Z) :=
  mpool_alloc_spec_aux st p iteration_bound.

End ALLOC.