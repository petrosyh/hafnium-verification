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
Section STORELOADSYNTACTICSUGAR.

  Definition debug_1 := "debug1".
  Definition debug_2 := "debug2".
  Definition debug_3 := "debug3".

  Definition store_and_load_at_i_debug  (p : var) (offset : Z) : stmt := 
    debug_1 #=  (Cast p tint) #;
            Put "store_at_i_debug: debug_1" debug_1 #;
            debug_2 #= (Vnormal (Vlong (Int64.repr (offset * 8)%Z))) #;
            Put "store_at_i_debug: debug_2" debug_2 #;
            debug_3 #= (debug_1 + debug_2) #;
            Put "store_at_i_debug: debug_3" debug_3 #;
            Put "store_at_i_debug: debug_3 ptr" (Cast debug_3 tptr).

  Definition store_at_i_debug  (p : var) (offset : Z) (e: expr): stmt := 
    debug_1 #=  (Cast p tint) #;
            Put "store_at_i_debug: debug_1" debug_1 #;
            debug_2 #= (Vnormal (Vlong (Int64.repr (offset * 8)%Z))) #;
            Put "store_at_i_debug: debug_2" debug_2 #;
            debug_3 #= (debug_1 + debug_2) #;
            Put "store_at_i_debug: debug_3" debug_3 #;
            Put "store_at_i_debug: debug_3 ptr" (Cast debug_3 tptr) #;
            (Cast debug_3 tptr) @ Int64.zero #:= e.
  
  Definition store_at_i (p : var) (offset : Z) (e: expr) : stmt :=
    ((Cast (Plus (Cast p tint) (Vnormal (Vlong (Int64.repr (offset * 8)%Z)))) tptr) @ Int64.zero #:= e).
    
  Definition load_at_i (p : var) (offset : Z) : expr :=
    (Cast (Plus (Cast p tint) (Vnormal (Vlong (Int64.repr (offset * 8))))) tptr) #@ Int64.zero.
  
End STORELOADSYNTACTICSUGAR.
  
Module MPOOLCONCURSTRUCT.

  (*
  struct mpool_chunk {
 	struct mpool_chunk *next_chunk;
	struct mpool_chunk *limit;
  };
   *)
  
  Definition next_chunk_loc := 0%Z.
  Definition limit_loc := 1%Z.

  (*
  struct mpool_entry {
	struct mpool_entry *next;
  };  
  *)

  Definition next_loc := 0%Z.
  
  (*
  struct mpool {
	struct spinlock lock;
	size_t entry_size;
	struct mpool_chunk *chunk_list;
	struct mpool_entry *entry_list;
	struct mpool *fallback;
  };
  *)

  Definition lock_loc := 0%Z.
  Definition entry_size_loc := 1%Z.
  Definition chunk_list_loc := 2%Z.
  Definition entry_list_loc := 3%Z.
  Definition fallback_loc := 4%Z.


End MPOOLCONCURSTRUCT.


Module MPOOLCONCUR.

  Import MPOOLCONCURSTRUCT.
  Import LangNotations.

  Definition mpool_locks_enabled := "mpool_locks_enabled".

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
    Put "mpool_lock: start" (load_at_i p lock_loc) #;
    #if mpool_locks_enabled
     then (Call "Lock.acquire" [CBV (load_at_i p lock_loc) ; CBV p])
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
    Put "mpool_unlock: start" (load_at_i p lock_loc) #;
    #if mpool_locks_enabled
     then (Call "Lock.release" [CBV (load_at_i p lock_loc) ; CBV p])
     else Skip.
  
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
    store_at_i p entry_size_loc entry_size #;
               store_at_i p chunk_list_loc Vnull #;
               store_at_i p entry_list_loc Vnull #;
               store_at_i p fallback_loc Vnull #;
               Put "mpool_init: initialization is done" p #;
               store_at_i p lock_loc (Call "Lock.new" []) #;
               Put "mpool_init: Lock new" p #;
               (Call "MPOOL.mpool_unlock" [CBR p]) #;
               Put "mpool_init: Lock unlock" p #;
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
    (Call "MPOOL.mpool_init" [CBR p; CBV (load_at_i from entry_size_loc)]) #;
      (Call "MPOOL.mpool_lock" [CBR from]) #; 
      (store_at_i p chunk_list_loc (load_at_i from chunk_list_loc)) #;
      (store_at_i p entry_list_loc (load_at_i from entry_list_loc)) #;
      (store_at_i p fallback_loc (load_at_i from fallback_loc)) #;
      (store_at_i from chunk_list_loc Vnull) #;
      (store_at_i from entry_list_loc Vnull) #;
      (store_at_i from fallback_loc Vnull) #;
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
        Call "MPOOL.mpool_init" [CBR p; CBV (load_at_i fallback entry_size_loc)] #;
        store_at_i p fallback_loc fallback #;
        Put "mpool_init_with_fallback: end" p.
    
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
    (* Need to make the following one as assume	
       if (!p->fallback) {
		return;
       }
     *)
    Put "mpool_fini: start" p #;        
    (Call "MPOOL.mpool_lock" [CBR p]) #;
    entry #= (load_at_i p entry_list_loc) #; 
    #while (#! (entry == Vnull))  
    do (
        ptr #= entry #;
            entry #= (load_at_i entry next_loc) #;
            (Call "MPOOL.mpool_free" [CBV (load_at_i p fallback_loc); CBR ptr])
      ) #;
        chunk #= (load_at_i p chunk_list_loc) #;
        #while (#! (chunk == Vnull))
        do (
            ptr #= chunk #;
                size #= (Cast (load_at_i chunk limit_loc) tint) - (Cast chunk tint) #;
                chunk #= (load_at_i chunk next_chunk_loc) #;
                (Call "MPOOL.mpool_add_chunk" [CBV (load_at_i p fallback_loc); CBR ptr; CBV size])
          ) #;
            (store_at_i p chunk_list_loc Vnull) #;
            (store_at_i p entry_list_loc Vnull) #;
            (store_at_i p fallback_loc Vnull) #;            
            (Call "MPOOL.mpool_unlock" [CBR p]) #;
            Put "mpool_end: start" p.      
           

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
  
  Definition mpool_add_chunk (p begin size : var) (new_begin new_end chunk: var) : stmt :=
    Put "mpool_add_chunk: start" p #;
        Put "mpool_add_chunk: load_at_i entry_size_loc" (load_at_i p entry_size_loc) #;
        new_begin #= (((Cast begin tint) + (load_at_i p entry_size_loc) - (Int64.repr 1))
                        / (load_at_i p entry_size_loc) * (load_at_i p entry_size_loc))
        #;
        new_end #= (((Cast begin tint) + size)
                      / (load_at_i p entry_size_loc) * (load_at_i p entry_size_loc))
        #;
        Put "mpool_add_chunk: new_begin" new_begin #;
        Put "mpool_add_chunk: new_end" new_end #;
        Put "mpool_add_chunk: load_at_limit_loc" (load_at_i p limit_loc) #;
        Put "mpool_add_chunk: condition1" (new_end <= new_begin) #;
        Put "mpool_add_chunk: condition2" ((new_end - new_begin) < (load_at_i p entry_size_loc)) #;
        Put "mpool_add_chunk: combined condition"
        ((new_end <= new_begin) #|| ((new_end - new_begin) < (load_at_i p entry_size_loc))) #;
        (#if (((new_end <= new_begin) #|| ((new_end - new_begin) < (load_at_i p entry_size_loc))))
          then
            Put "mpool_add_chunk: failed" p #;
            Return Vfalse
          else
            (Call "MPOOL.mpool_lock" [CBR p])
              #;
              (* (store_and_load_at_i_debug chunk limit_loc) #; *)
              (store_at_i_debug chunk limit_loc (Cast new_end tptr)) #;
              Put "mpool_add_chunk: store new_end" (Cast new_end tptr) #;
              (store_at_i chunk limit_loc (Cast new_end tptr)) #;
              
              (* It works now *)
              chunk #= (Cast new_begin tptr) #;
              (store_at_i p chunk_list_loc chunk) #;

              
              (Call "MPOOL.mpool_unlock" [CBR p]) #;
              Put "mpool_add_chunk: store chunk" chunk #;
              Put "mpool_add_chunk: succeed" p #;
              Put "mpool_add_chunk: end" (load_at_i p limit_loc) #;
              Put "mpool_add_chunk: load_at_i entry_size_loc" (load_at_i p entry_size_loc) #;
              Put "mpool_add_chunk: load_at_i chunk_list" (load_at_i p chunk_list_loc) #;
              Put "mpool_add_chunk: load_at_i entry_list" (load_at_i p entry_list_loc) #;
              Put "mpool_add_chunk: load_at_i entry_list" (load_at_i p fallback_loc) #;
              Return Vtrue).
  
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
    e #= ptr #;
      (Call "MPOOL.mpool_lock" [CBR p]) #;
      (store_at_i e next_loc (load_at_i p entry_list_loc)) #;
      (store_at_i p entry_list_loc e) #;
      (Call "MPOOL.mpool_unlock" [CBR p]) #;
      Put "mpool_free: end" p.
      
  
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

  Definition mpool_alloc_contiguous_no_fallback
             (p count align: var)
             (prev ret chunk start new_chunk: var): stmt :=
    Put "mpool_alloc_contiguous_no_fallback: start" p #;            
    ret #= Vnull #;
    align #= (align * (load_at_i p entry_size_loc))
    #;
    (Call "MPOOL.mpool_lock" [CBR p]) #;
    prev #= (load_at_i p chunk_list_loc) #;
    Put "mpool_alloc_contiguous_no_fallback: prev value" prev #;
    Put "mpool_alloc_contiguous_no_fallback: vnull value" Vnull #;
    Put "mpool_alloc_contiguous_no_fallback: initial condition" (prev == Vnull) #;
    #while (#! (prev == Vnull))
    do (
        Put "mpool_alloc_contiguous_no_fallback: while" p #;            
            chunk #= prev #;
            start #= ((((Cast chunk tint) * align - (repr 1)) / align) * align)
            #;
            new_chunk #= (Cast (start + (count * (load_at_i p entry_size_loc))) tptr) #;
            (#if ((Cast new_chunk tint) <= (Cast (load_at_i chunk limit_loc) tint))
              then (#if ((Cast new_chunk tint) <= (Cast (load_at_i chunk limit_loc) tint))
                     then prev #= (load_at_i chunk next_chunk_loc)
                     else new_chunk #= chunk #;
                                    prev #= new_chunk)
                     #;
                     (#if ((load_at_i p entry_size_loc) <= start - (Cast chunk tint))
                       then (store_at_i chunk next_chunk_loc prev)
                              #;
                              prev #= chunk #; 
                              (store_at_i chunk limit_loc (Cast start tptr))
                       else Skip) #;
                     ret #= (Cast start tptr) #;
                     Break
              else Skip) #;
            prev #= (load_at_i chunk next_chunk_loc)
      ) #;
        (Call "MPOOL.mpool_unlock" [CBR p]) #;
        Put "mpool_alloc_contiguous_no_fallback: end value" p #;            
        Put "mpool_alloc_contiguous_no_fallback: ret value" ret #;            
        Return ret.
         
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
         Debug "looping mpool_alloc_contiguous" Vnull #;
               ret #= (Call "MPOOL.mpool_alloc_contiguous_no_fallback" [CBR p ; CBV count; CBV align]) #;
               #if (ret)
                then
                  Put "mpool_alloc_contiguous: end" p #;         
                      Return ret
                else Skip #;
                          p #= (load_at_i p fallback_loc)
                          #;
                          #if (p)
                           then Skip
                           else Break
       ) #;
         Put "mpool_alloc_contiguous: end" p #;         
         Return Vnull.
        

  Definition mpool_init_locksF: function. mk_function_tac mpool_init_locks ([]: list var) ([]: list var). Defined.
  Definition mpool_enable_locksF: function. mk_function_tac mpool_enable_locks ([]: list var) ([]: list var). Defined.
  Definition mpool_lockF: function. mk_function_tac mpool_lock ["p"] ([]: list var). Defined. 
  Definition mpool_unlockF: function. mk_function_tac mpool_unlock ["p"] ([]: list var). Defined.
  Definition mpool_initF: function. mk_function_tac mpool_init ["p"; "entry_size"] ([]: list var). Defined.
  Definition mpool_init_fromF: function. mk_function_tac mpool_init_from ["p"; "from"] ([]: list var). Defined.
  Definition mpool_init_with_fallbackF: function.
    mk_function_tac mpool_init_with_fallback ["p"; "fallback"] ([]: list var). Defined.
  Definition mpool_finiF: function.
    mk_function_tac mpool_fini ["p"] ["entry"; "chunk"; "ptr"; "size"]. Defined.
  Definition mpool_add_chunkF: function.
    mk_function_tac mpool_add_chunk ["p"; "begin"; "size"] ["new_begin"; "new_end"; "chunk"]. Defined.
  Definition mpool_freeF: function.
    mk_function_tac mpool_free ["p"; "ptr"] ["e"]. Defined.
  Definition mpool_alloc_contiguous_no_fallbackF: function.
    mk_function_tac mpool_alloc_contiguous_no_fallback ["p"; "count"; "align"]
                    ["prev"; "ret"; "chunk"; "start"; "new_chunk"]. Defined.
  Definition mpool_alloc_contiguousF: function.
    mk_function_tac mpool_alloc_contiguous ["p"; "count"; "align"] ["ret"]. Defined.


  Definition mpool_program: program :=
      [
        ("MPOOL.mpool_init_locks", mpool_init_locksF) ;
      ("MPOOL.mpool_enable_locks", mpool_enable_locksF) ;
      ("MPOOL.mpool_lock", mpool_lockF) ;
      ("MPOOL.mpool_unlock", mpool_unlockF) ;
      ("MPOOL.mpool_init", mpool_initF) ;
      ("MPOOL.mpool_init_from", mpool_init_fromF) ;
      ("MPOOL.mpool_init_with_fallback", mpool_init_with_fallbackF) ;
      ("MPOOL.mpool_add_chunk", mpool_add_chunkF) ;
      ("MPOOL.mpool_free", mpool_freeF) ;
      ("MPOOL.mpool_alloc_contiguous_no_fallback", mpool_alloc_contiguous_no_fallbackF) ;
      ("MPOOL.mpool_alloc_contiguous",  mpool_alloc_contiguousF)
      ].
  
  Definition mpool_modsem : ModSem := program_to_ModSem mpool_program.
    
End MPOOLCONCUR.

