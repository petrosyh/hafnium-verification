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
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Set Implicit Arguments.

Section STORELOADSYNTACTICSUGAR.
  
  Definition store_at_i (p : var) (offset : Z) (e: expr) : stmt :=
    (* Put " " i#; *)
    Store (Cast (Plus (Cast p tint) (repr offset)) tptr) e.

  Definition load_at_i (p : var) (offset : Z) : expr :=
    (* Put " " i#; *)
    Load (Cast (Plus (Cast p tint) (repr offset)) tptr).
  
End STORELOADSYNTACTICSUGAR.
  
Module MPOOLCONCUR.

  (*
  struct mpool_chunk {
 	struct mpool_chunk *next_chunk;
	struct mpool_chunk *limit;
  };
   *)
  
  Definition next_chunk_loc := 0.
  Definition limit_loc := 1.

  (*
  struct mpool_entry {
	struct mpool_entry *next;
  };  
  *)

  Definition next_loc := 0.
  
  (*
  struct mpool {
	struct spinlock lock;
	size_t entry_size;
	struct mpool_chunk *chunk_list;
	struct mpool_entry *entry_list;
	struct mpool *fallback;
  };
  *)

  Definition lock_loc := 0.
  Definition entry_size_loc := 1.
  Definition chunk_list_loc := 2.
  Definition entry_list_loc := 3.
  Definition fallback_loc := 4.

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
    store_at_i p entry_size_loc entry_size #;
               store_at_i p chunk_list_loc Vnull #;
               store_at_i p entry_list_loc Vnull #;
               store_at_i p fallback_loc Vnull #;
               store_at_i p lock_loc (Call "Lock.new" []) #;
               (Call "MPOOL.mpool_unlock" [CBR p]).

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
    (Call "MPOOL.mpool_init" [CBR p; CBV (load_at_i from entry_size_loc)]) #;
      (Call "MPOOL.mpool_lock" [CBR from]) #; 
      (store_at_i p chunk_list_loc (load_at_i from chunk_list_loc)) #;
      (store_at_i p entry_list_loc (load_at_i from entry_list_loc)) #;
      (store_at_i p fallback_loc (load_at_i from fallback_loc)) #;
      (store_at_i from chunk_list_loc Vnull) #;
      (store_at_i from entry_list_loc Vnull) #;
      (store_at_i from fallback_loc Vnull) #;
      (Call "MPOOL.mpool_unlock" [CBR from]).
      
  (*
  void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback)
  {
	mpool_init(p, fallback->entry_size);
	p->fallback = fallback;
  }
  *)

  Definition mpool_init_with_fallback (p fallback: var) : stmt :=
    Call "MPOOL.mpool_init" [CBR p; CBV (load_at_i fallback entry_size_loc)] #;
         store_at_i p fallback_loc fallback.

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
            (Call "MPOOL.mpool_unlock" [CBR p]).

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
    new_begin #= ((Cast begin tint) + (load_at_i p entry_size_loc) - (repr 1)) /
              (load_at_i p entry_size_loc) * (load_at_i p entry_size_loc) #;
    new_end #= ((Cast begin tint) + size) /
              (load_at_i p entry_size_loc) * (load_at_i p entry_size_loc) #;
    #if ((new_end <= new_begin) #|| ((load_at_i p entry_size_loc) < (new_end - new_begin))) 
     then Return Vfalse
     else
       chunk #= (Cast new_begin tptr) #;
             (store_at_i chunk limit_loc (Cast new_end tptr)) #;
             (store_at_i p chunk_list_loc chunk) #;
             (Call "MPOOL.mpool_unlock" [CBR p]) #;
             Return Vtrue.


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
    e #= ptr #;
      (Call "MPOOL.mpool_lock" [CBR p]) #;
      (store_at_i e next_loc (load_at_i p entry_list_loc)) #;
      (store_at_i p entry_list_loc e) #;
      (Call "MPOOL.mpool_unlock" [CBR p]).
  
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
    ret #= Vnull #;
        align #= align * (load_at_i p entry_size_loc) #;
        (Call "MPOOL.mpool_lock" [CBR p]) #;     
        prev #= (load_at_i p chunk_list_loc) #;
        #while (#! prev == Vnull)
        do (
            chunk #= prev #;
                  start #= (((Cast chunk tint) * align - (repr 1)) / align) * align #;
                  new_chunk #= (Cast (start + (count * (load_at_i p entry_size_loc))) tptr) #;
                  (#if ((Cast new_chunk tint) <= (Cast (load_at_i chunk limit_loc) tint))
                    then (#if ((Cast new_chunk tint) <= (Cast (load_at_i chunk limit_loc) tint))
                           then prev #= (load_at_i chunk next_chunk_loc)
                           else new_chunk #= chunk #;
                                          prev #= new_chunk) #;
                         (#if ((load_at_i p entry_size_loc) <= start - (Cast chunk tint))
                           then (store_at_i chunk next_chunk_loc prev) #;
                                prev #= chunk #; 
                                (store_at_i chunk limit_loc (Cast start tptr))
                           else Skip) #;
                         ret #= (Cast start tptr) #;
                         Break
                    else Skip) #;
                  prev #= (load_at_i chunk next_chunk_loc)
          ) #;
            (Call "MPOOL.mpool_unlock" [CBR p]) #;
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
    #while Vtrue
     do (
         Debug "looping mpool_alloc_contiguous" Vnull #;
               ret #= (Call "MPOOL.mpool_alloc_contiguous_no_fallback" [CBR p ; CBV count; CBV align]) #;
               #if (ret)
                then Return ret
                else Skip #;
                          p #= (load_at_i p fallback_loc)
                          #;
                          #if (p)
                           then Skip
                           else Break
       ) #;
         Return Vnull.

End MPOOLCONCUR.

