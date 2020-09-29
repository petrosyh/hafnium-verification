(*
 * Copyright 2020 Jieung Kim
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

Set Implicit Arguments.

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
  
  Definition store_at_i (p : var) (offset : Z) (e: expr) : stmt :=
    ((Cast (Plus (Cast p tint) (Vnormal (Vlong (Int64.repr (offset * 8)%Z)))) tptr) @ Int64.zero #:= e).
  
  Definition load_at_i (p : var) (offset : Z) : expr :=
    (Cast (Plus (Cast p tint) (Vnormal (Vlong (Int64.repr offset)))) tptr) #@ Int64.zero.
  
End STORELOADSYNTACTICSUGAR.

(* Some dependencies: 
   1. inc/hf/addr.h - some address translations and type definitions such as paddr_t and so on 
   2. inc/hf/arch/cpu.h - 5 depends on this file
   3. src/arch/arch64/cpu.c - 5 depends on this file
   4. inc/hf/arch/mm.h - a header file for 4. 
   5. src/arch/arch64/mm.c - several simple functions are used in src/mm.c
   6. inc/hf/mm.h - a header file for this mm.c
   7. src/mpool.c 
   8. inc/hf/mpool
   9. inc/hf/layout.c
  10. src/layout.c
*)

Module MMCONCURSTRUCT.

  (*
  #define MM_PPOOL_ENTRY_SIZE sizeof(struct mm_page_table)
  *)

  Definition MM_PPOOL_ENTRY_SIZE := (mul MM_PTE_PER_PAGE sizeof_pte_t).

  (*
  struct mm_page_table {
	alignas(PAGE_SIZE) pte_t entries[MM_PTE_PER_PAGE];
  };
  *)

  Definition entries_size := (unsigned MM_PTE_PER_PAGE)%Z.
  Definition entries_head_loc := 0%Z.
  Definition entries_tail_loc := ((unsigned MM_PTE_PER_PAGE) - 1)%Z.

  (*
  struct mm_ptable {
	/** Address of the root of the page table. */
	paddr_t root;
  };
   *)
  
  Definition root_loc := 0%Z.

  (*
  /** The type of addresses stored in the page table. */
  typedef uintvaddr_t ptable_addr_t;
  *)

  (*
  /** Represents the currently locked stage-1 page table of the hypervisor. */
  struct mm_stage1_locked {
	struct mm_ptable *ptable;
  };
   *)
  Definition ptable_loc := 0%Z.

 
End MMCONCURSTRUCT.

Module MMCONCUR.

  Import MMCONCURSTRUCT.

  
  (*
  static struct mm_ptable ptable;
  static struct spinlock ptable_lock;

  static bool mm_stage2_invalidate = false;  
   *)


  Definition ptable := "ptable".
  Definition ptable_lock := "ptable_lock".
  Definition mm_stage2_invalidate := "mm_stage2_invalidate".

  (* No matching function, but it has to be used in the test cases *)
  Definition mm_stage2_invalidate_false :=
    mm_stage2_invalidate #= Vfalse. 

  (*
  /**
   * After calling this function, modifications to stage-2 page tables will use
   * break-before-make and invalidate the TLB for the affected range.
   */
   void mm_vm_enable_invalidation(void)
   {
 	mm_stage2_invalidate = true;
  }
  *)

  (* No matching function, but it has to be used in the test cases *)
  Definition  mm_vm_enable_invalidation :=
    mm_stage2_invalidate #= Vtrue. 

  
  (*
  /**
   * Get the page table from the physical address.
   */
  static struct mm_page_table *mm_page_table_from_pa(paddr_t pa)
  {
          return ptr_from_va(va_from_pa(pa));
  }
   *)

  Definition mm_page_table_from_pa (pa: var) :=
    Return (Call "ADDR.ptr_from_va" [CBV (Call "ADDR.va_from_pa" [CBV pa])]).
  
  (*
  // JIEUNG:find out the first address(?) 
  /**
   * Rounds an address down to a page boundary.
   */
  static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr)
  {
          return addr & ~((ptable_addr_t)(PAGE_SIZE - 1));
  }
   *)

  (* XXX: Do we need to consider (ptable_addr_t) casting in here? *)
  Definition mm_round_down_to_page (addr: var) :=
    Return (addr #& (#~ (PAGE_SIZE - one))).
  
  (*
  /**
   * Rounds an address up to a page boundary.
   */
  static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr)
  {
          return mm_round_down_to_page(addr + PAGE_SIZE - 1);
  }
   *)

  Definition mm_round_up_to_page (addr: var) :=
    Return (Call "MM.mm_round_down_to_page" [CBV (addr + PAGE_SIZE - one)]).  
  
  (*
  // JIEUNG: PAGE_BITS = 12
  // JIEUNG: PAGE_LEVEL_BITS = 9
  // if level = 3 --> 2 ^ (3 * 9 + 12)
  /**
   * Calculates the size of the address space represented by a page table entry at
   * the given level.
   */
  static size_t mm_entry_size(uint8_t level)
  {
          return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
  }
  *)

  Definition mm_entry_size (level : var) :=
    Return (UINT64_C(one) #<< (PAGE_BITS + (level * PAGE_LEVEL_BITS))).
  
  (*
  /**
   * Gets the address of the start of the next block of the given size. The size
   * must be a power of two.
   */
  static ptable_addr_t mm_start_of_next_block(ptable_addr_t addr,
          				    size_t block_size)
  {
          return (addr + block_size) & ~(block_size - 1);
  }
   *)
  
  Definition mm_start_of_next_block (addr block_size : var) :=
    Return ((addr + block_size) #& (#~ (block_size - one))).
  
  (*   
  /**
   * Gets the physical address of the start of the next block of the given size.
   * The size must be a power of two.
   */
  static paddr_t mm_pa_start_of_next_block(paddr_t pa, size_t block_size)
  {
          return pa_init((pa_addr(pa) + block_size) & ~(block_size - 1));
  }
   *)


  
  Definition mm_pa_start_of_next_block (pa block_size : var) :=
    Return (Call "ADDR.pa_init"
                 [CBV (((Call "ADDR.pa_addr" [CBV pa]) + block_size)
                         #& (#~ (block_size - one)))]).
  
  (* 
  /**
   * For a given address, calculates the maximum (plus one) address that can be
   * represented by the same table at the given level.
   */
  static ptable_addr_t mm_level_end(ptable_addr_t addr, uint8_t level)
  {
          size_t offset = PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS;
   
          return ((addr >> offset) + 1) << offset;
  }
  *)

  Definition mm_level_end (addr level : var) (offset : var) :=
    offset #= (PAGE_BITS + ((level + one) * PAGE_LEVEL_BITS)) #;
           Return (((addr #>> offset) + one) #<< offset).
    
  
  (*
  // JIEUNG: find out the value based on the address and level and ... 
  /**
   * For a given address, calculates the index at which its entry is stored in a
   * table at the given level.
   */
  static size_t mm_index(ptable_addr_t addr, uint8_t level)
  {
          ptable_addr_t v = addr >> (PAGE_BITS + level * PAGE_LEVEL_BITS);
   
          return v & ((UINT64_C(1) << PAGE_LEVEL_BITS) - 1);
  }
   *)

  Definition mm_index (addr level : var) (v : var) :=
    v #= (addr #>> (PAGE_BITS + (level * PAGE_LEVEL_BITS))) #;
      Return (v #& ((UINT64_C(one) #<< PAGE_LEVEL_BITS) - one)).

  (*
  /*********************************************************************
   *
   * Above functions are auxiliary functions
   *
   * *******************************************************************/
   
  /**
   * Allocates a new page table.
   */
  static struct mm_page_table *mm_alloc_page_tables(size_t count,
          					  struct mpool *ppool)
  {
          if (count == 1) {
          	return mpool_alloc(ppool);
          }
   
          return mpool_alloc_contiguous(ppool, count, count);
  }
   *)

  (* XXX: original version
  Definition mm_alloc_page_tables (count ppool : var) :=
    #if (count == one)
     then (Call "MPOOL.mpool_alloc_contiguous" [CBR ppool; CBV one; CBV one])
     else (Call "MPOOL.mpool_alloc_contiguous" [CBR ppool; CBV count; CBV count]).
  *)  

  (* XXX: simplified version *)
  Definition mm_alloc_page_tables (count ppool : var) : stmt :=
    (Call "MPOOL.mpool_alloc_contiguous" [CBR ppool; CBV count; CBV count]).
  
  (*
  // JIEUNG: this function is an auxiliary function to find out max level of both
  // stages
  /**
   * Returns the maximum level in the page table given the flags.
   */
  static uint8_t mm_max_level(int flags)
  {
          return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_max_level()
          				: arch_mm_stage2_max_level();
  }
  *)   

  Definition mm_max_level (flags: var) :=
    #if (flags #& MM_FLAG_STAGE1) 
     then Return (Call "ARCHMM.arch_mm_stage1_max_level" [])
     else Return (Call "ARCHMM.arch_mm_stage2_max_level" []).
  
(*
  // JIEUNG: this function is an auxiliary function to find 
  // out max number of pages in the table
  /**
  * Returns the number of root-level tables given the flags.
   */
   static uint8_t mm_root_table_count(int flags)
  {       
          return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_root_table_count()
          				: arch_mm_stage2_root_table_count();
  }
  *)

  Definition mm_root_table_count (flags: var) :=
    #if (flags #& MM_FLAG_STAGE1) 
     then Return (Call "ARCHMM.arch_mm_stage1_root_table_count" [])
     else Return (Call "ARCHMM.arch_mm_stage2_root_table_count" []).
  
  (*
  // JIEUNG: we will not model the following function
  /**
   * Invalidates the TLB for the given address range.
   */
  static void mm_invalidate_tlb(ptable_addr_t begin, ptable_addr_t end, int flags)
  {
          if (flags & MM_FLAG_STAGE1) {
          	arch_mm_invalidate_stage1_range(va_init(begin), va_init(end));
          } else {
          	arch_mm_invalidate_stage2_range(ipa_init(begin), ipa_init(end));
          }
  }
  *)

  Definition mm_invalidate_tlb (a_begin a_end flags : var) :=
    #if (flags #& MM_FLAG_STAGE1) 
     then Return (Call "ARCHMM.arch_mm_invalidate_stage1_range"
                       [CBV (Call "ADDR.va_init" [CBV a_begin]);
                       CBV (Call "ADDR.va_init" [CBV a_end])])
     else Return (Call "ARCHMM.arch_mm_invalidate_stage2_range"
                       [CBV (Call "ADDR.ipa_init" [CBV a_begin]);
                       CBV (Call "ADDR.ipa_init" [CBV a_end])]).

  (*
  /**
   * Frees all page-table-related memory associated with the given pte at the
   * given level, including any subtables recursively.
   */
  static void mm_free_page_pte(pte_t pte, uint8_t level, struct mpool *ppool)
  {
          struct mm_page_table *table;
          uint64_t i;
   
          if (!arch_mm_pte_is_table(pte, level)) {
          	return;
          }
   
          /* Recursively free any subtables. */
          table = mm_page_table_from_pa(arch_mm_table_from_pte(pte, level));
          for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
          	mm_free_page_pte(table->entries[i], level - 1, ppool);
          }
   
          /* Free the table itself. */
          mpool_free(ppool, table);
  }
   *)



  (* XXX: Need to refactor this definition *) 
  Definition expr_to_int (e : expr) :=
    match e with
    | Val n => match n with
               | Vnormal (Vlong n') => n'
               | _ => (repr max_unsigned)
               end
    | _ => (repr max_unsigned)
    end.

    
  Definition mm_free_page_pte (pte level ppool : var) (table i : var) :=
    (* XXX: This condition should be written as a pre condition  
          if (!arch_mm_pte_is_table(pte, level)) {
          	return;
          }
     *)
    table #= (Call "MM.mm_page_table_from_pa"
                   [CBV (Call "ARCHMM.arch_mm_table_from_pte" [CBR pte; CBV level])]) #;
          i #= zero #;
          #while (i < MM_PTE_PER_PAGE)
          do (
              (* XXX :CBV at the first one is a little bit wierd, because it is a pointer... 
                      Need to set the criteria for CBV and CBR *) 
              (Call "MM.mm_free_page_pte"
                    [CBV (load_at_i table (unsigned (expr_to_int (Var i)))); CBV (level - one); CBR ppool]) #;
                i #= i + one
            ) #;
              (Call "MPOOL.mpool_free" [CBR ppool; CBR table]).
     
  (*
  // JIEUNG: this sets the range of address space 
  /**
   * Returns the first address which cannot be encoded in page tables given by
   * `flags`. It is the exclusive end of the address space created by the tables.
   */
  ptable_addr_t mm_ptable_addr_space_end(int flags)
  {
          return mm_root_table_count(flags) *
                 mm_entry_size(mm_max_level(flags) + 1);
  }
   *)

  Definition mm_ptable_addr_space_end (flags : var) :=
    Return ((Call "MM.mm_root_table_count" [CBV flags]) *
            (Call "MM.mm_entry_size" [CBV ((Call "MM.mm_max_level" [CBV flags]) + one)])).
   
  (*
  /**
   * Initialises the given page table.
   */
  bool mm_ptable_init(struct mm_ptable *t, int flags, struct mpool *ppool)
  {
          uint8_t i;
          size_t j;
          struct mm_page_table *tables;
          // JIEUNG: mm_root_table_count :
          // return arch_mm_stage2_root_table_count() or
          // arch_mm_stage1_root_table_count()
          uint8_t root_table_count = mm_root_table_count(flags);
   
          /* JIEUNG:
           uint8_t arch_mm_stage1_root_table_count(void)
           { return 1; }
   
           uint8_t arch_mm_stage2_root_table_count(void)
           { return mm_s2_root_table_count; }
           */
   
          /* JIEUNG: if root_table_count is 1 
           * -> then call mpool_alloc
           * -> then call mpool_alloc_contiguous 
           */
          tables = mm_alloc_page_tables(root_table_count, ppool);
          if (tables == NULL) {
          	return false;
          }
   
          // JIEUNG: if it is allocated
          // root_table_count is defined in arch_mm_stage1_root_table_count()
                                   /** JIEUNG:
                                    * Returns the encoding of a page table entry that isn't present.
                                    */
                                   /*
                                   pte_t arch_mm_absent_pte(uint8_t level)
                                   {
                                           (void)level;
                                           return 0;
                                   }
                                   */ 
          for (i = 0; i < root_table_count; i++) {
          	for (j = 0; j < MM_PTE_PER_PAGE; j++) {
          		tables[i].entries[j] =
          			arch_mm_absent_pte(mm_max_level(flags));
          	}
          }
   
          /*
           * TODO: halloc could return a virtual or physical address if mm not
           * enabled?
           */
          t->root = pa_init((uintpaddr_t)tables);
   
          return true;
  }
   *)

  
  Definition mm_ptable_init (t flags ppool: var) (root_table_count tables i j: var) :=
    root_table_count #= (Call "MM.mm_root_table_count" [CBV flags]) #;
                     tables #= (Call "MM.mm_alloc_page_tables" [CBV root_table_count; CBR ppool]) #;
                     (#if (tables == Vnull)
                      then
                        Return Vfalse
                      else Skip) #;
                     (* XXX: Add this condition as an assumption
                     if (tables == NULL) {
          	       return false;
                     } *)
                     i #= zero #;
                     #while (i < root_table_count)
                     do (
                         j #= zero #;
                           #while (j < MM_PTE_PER_PAGE)
                           do (
                               (store_at_i
                                  (* XXX: can we simplify this line or can we make thie one with better readability? *)
                                  tables ((unsigned (expr_to_int (Var i))) * entries_size +
                                          (unsigned (expr_to_int (Var j))))
                                  (Call "ARCHMM.arch_mm_absent_pte" [CBV (Call "MM.mm_max_level" [CBV flags])])) #;
                               j #= j + one
                             ) #;
                               i #= i + one
                       ) #;
                         (store_at_i t root_loc (Call "ADDR.pa_init" [CBV (Cast tables tint)])) #;
                         Return Vtrue.                       
  

  (*
  /**
   * Frees all memory associated with the give page table.
   */
  static void mm_ptable_fini(struct mm_ptable *t, int flags, struct mpool *ppool)
  {
   
    // JIEUNG: find out the address 
          struct mm_page_table *tables = mm_page_table_from_pa(t->root);
          uint8_t level = mm_max_level(flags);
          uint8_t root_table_count = mm_root_table_count(flags);
          uint8_t i;
          uint64_t j;
   
          for (i = 0; i < root_table_count; ++i) {
          	for (j = 0; j < MM_PTE_PER_PAGE; ++j) {
          		mm_free_page_pte(tables[i].entries[j], level, ppool);
          	}
          }
   
          // JIEUNG: root_table_count is calculated at the initialization 
          mpool_add_chunk(ppool, tables,
          		sizeof(struct mm_page_table) * root_table_count);
  }
   *)


  (* XXX: sizeof(struct mm_page_table): how can we support this one? *)                        
  Definition  mm_page_table_size := MM_PPOOL_ENTRY_SIZE.                         
  Definition  mm_ptable_fini (t flags ppool : var) (tables root_table_count level i j : var) := 
    (* XXX: CBV in here is somewhat wierd *)
    tables #= (Call "MM.mm_page_table_from_pa" [CBV (load_at_i t root_loc)]) #;
           level #= (Call "MM.mm_max_level" [CBV flags]) #;
           root_table_count #= (Call "MM.mm_root_table_count" [CBV flags]) #;
           i #= zero #;
           #while (i < root_table_count)
           do (
               j #= zero #;
                 #while (j < MM_PTE_PER_PAGE)
                 do (
                     (Call "MM.mm_free_page_pte"
                           [CBV (load_at_i tables ((unsigned (expr_to_int (Var i))) * entries_size +
                                                   (unsigned (expr_to_int (Var j)))));
                           CBV level; CBR ppool]) #;
                                                  j #= j + one
                   ) #;
                     i #= i + one
             ) #;
               (Call "MPOOL.mpool_add_chunk" [CBR ppool; CBR tables; CBV (mm_page_table_size * root_table_count)]).
    
  
  (* 
  /**
   * Replaces a page table entry with the given value. If both old and new values
   * are valid, it performs a break-before-make sequence where it first writes an
   * invalid value to the PTE, flushes the TLB, then writes the actual new value.
   * This is to prevent cases where CPUs have different 'valid' values in their
   * TLBs, which may result in issues for example in cache coherency.
   */
  static void mm_replace_entry(ptable_addr_t begin, pte_t *pte, pte_t new_pte,
          		     uint8_t level, int flags, struct mpool *ppool)
  {
          pte_t v = *pte;
   
          /*
           * We need to do the break-before-make sequence if both values are
           * present and the TLB is being invalidated.
           */
   
          // JIEUNG: it depends on the STAGE. So, in our testing we have to cover
          // both
          if (((flags & MM_FLAG_STAGE1) || mm_stage2_invalidate) &&
              arch_mm_pte_is_valid(v, level) &&
              arch_mm_pte_is_valid(new_pte, level)) {
          	*pte = arch_mm_absent_pte(level);
          	mm_invalidate_tlb(begin, begin + mm_entry_size(level), flags);
          }
   
          /* Assign the new pte. */
          *pte = new_pte;
   
          /* Free pages that aren't in use anymore. */
          mm_free_page_pte(v, level, ppool);
  }
   *)

  Definition mm_replace_entry (a_begin pte new_pte level flags ppool : var) (v : var) :=    
    v #= pte #;
      (#if (((flags #& MM_FLAG_STAGE1) #|| mm_stage2_invalidate)
             #&&
             (Call "ARCHMM.arch_mm_pte_is_valid" [CBR v; CBV level])
             #&&
             (Call "ARCHMM.arch_mm_pte_is_valid" [CBR new_pte; CBV level]))
        then pte #= (Call "ARCHMM.arch_mm_absent_pte" [CBV level]) #;
                 (Call "MM.mm_invalidate_tlb" [CBV a_begin; CBV (a_begin + (Call "MM.mm_entry_size" [CBV level]));
                                              CBV flags])
        else Skip) #;
      pte #= new_pte #;
      (Call "MM.mm_free_page_pte" [CBR v; CBV level; CBR ppool]).
                                                                
    
  (*
  /**
   * Populates the provided page table entry with a reference to another table if
   * needed, that is, if it does not yet point to another table.
   *
   * Returns a pointer to the table the entry now points to.
   */
  static struct mm_page_table *mm_populate_table_pte(ptable_addr_t begin,
          					   pte_t *pte, uint8_t level,
          					   int flags,
          					   struct mpool *ppool)
  {
          struct mm_page_table *ntable;
          pte_t v = *pte;
          pte_t new_pte;
          size_t i;
          size_t inc;
          uint8_t level_below = level - 1;
   
          /* Just return pointer to table if it's already populated. */
          if (arch_mm_pte_is_table(v, level)) {
          	return mm_page_table_from_pa(arch_mm_table_from_pte(v, level));
          }
   
          /* Allocate a new table. */
          ntable = mm_alloc_page_tables(1, ppool);
          if (ntable == NULL) {
          	dlog_error("Failed to allocate memory for page table\n");
          	return NULL;
          }
   
          /* Determine template for new pte and its increment. */
          if (arch_mm_pte_is_block(v, level)) {
          	inc = mm_entry_size(level_below);
          	new_pte = arch_mm_block_pte(level_below,
          				    arch_mm_block_from_pte(v, level),
          				    arch_mm_pte_attrs(v, level));
          } else {
          	inc = 0;
          	new_pte = arch_mm_absent_pte(level_below);
          }
   
          /* Initialise entries in the new table. */
          for (i = 0; i < MM_PTE_PER_PAGE; i++) {
          	ntable->entries[i] = new_pte;
          	new_pte += inc;
          }
   
          /* Ensure initialisation is visible before updating the pte. */
          atomic_thread_fence(memory_order_release);
   
   
          // JIEUNG: typedef uintptr_t uintpaddr_t;
   
          /* Replace the pte entry, doing a break-before-make if needed. */
          mm_replace_entry(begin, pte,
          		 arch_mm_table_pte(level, pa_init((uintpaddr_t)ntable)),
          		 level, flags, ppool);
   
          return ntable;
  }
   *)

  Definition mm_populate_table_pte (a_begin pte level flags ppool : var) (ntable v new_pte i inc level_below : var) :=
    (* XXX: do we have a good idea about pointer alaising? *)
    v #= pte #;
      level_below #= (level - one) #;
      (#if (Call "ARCHMM.arch_mm_pte_is_table" [CBR v; CBV level])
        then Return (Call "MM.mm_page_table_from_pa" [CBV (Call "ARCHMM.arch_mm_table_from_pte" [CBR v; CBV level])])
        else Skip) #;
      ntable #= (Call "MM.mm_alloc_page_tables" [CBV one; CBR ppool]) #;
      (#if (ntable == Vnull) then Return Vnull else Skip) #;
      (#if (Call "ARCHMM.arch_mm_pte_is_block" [CBR v; CBV level])
        then inc #= (Call "MM.mm_entry_size" [CBV level_below]) #;
                 new_pte #= (Call "ARCHMM.arch_mm_block_pte"
                                  [CBV level_below;
                                  CBV (Call "ARCHMM.arch_mm_block_from_pte" [CBR v; CBV level]);
                                  CBV (Call "ARCHMM.arch_mm_pte_attrs" [CBR v; CBV level])])
        else inc #= zero #;
                 new_pte #= (Call "ARCHMM.arch_mm_absent_pte" [CBV level_below])) #;
      i #= zero #;
      #while (i < MM_PTE_PER_PAGE)
      do (
        (store_at_i ntable (unsigned (expr_to_int (Var i))) new_pte) #;
          new_pte #= (new_pte + inc) #;
          i #= (i + one)
        ) #;
          (Call "MM.mm_replace_entry" [CBV a_begin; CBR pte;
                                      CBV (Call "ARCHMM.arch_mm_table_pte"
                                                [CBV level;
                                                CBV (Call "ADDR.pa_init" [CBV (Cast ntable tint)])]);
                                      CBV level; CBV flags; CBR ppool]) #;
          Return ntable.

  (*
  /**
   * Updates the page table at the given level to map the given address range to a
   * physical range using the provided (architecture-specific) attributes. Or if
   * MM_FLAG_UNMAP is set, unmap the given range instead.
   *
   * This function calls itself recursively if it needs to update additional
   * levels, but the recursion is bound by the maximum number of levels in a page
   * table.
   */
  static bool mm_map_level(ptable_addr_t begin, ptable_addr_t end, paddr_t pa,
          		 uint64_t attrs, struct mm_page_table *table,
          		 uint8_t level, int flags, struct mpool *ppool)
  {
          pte_t *pte = &table->entries[mm_index(begin, level)];
          ptable_addr_t level_end = mm_level_end(begin, level);
          size_t entry_size = mm_entry_size(level);
          bool commit = flags & MM_FLAG_COMMIT;
          bool unmap = flags & MM_FLAG_UNMAP;
   
          /* Cap end so that we don't go over the current level max. */
          if (end > level_end) {
          	end = level_end;
          }
   
          /* Fill each entry in the table. */
          while (begin < end) {
          	if (unmap ? !arch_mm_pte_is_present( *pte, level)
          		  : arch_mm_pte_is_block( *pte, level) &&
          			    arch_mm_pte_attrs( *pte, level) == attrs) {
          		/*
          		 * If the entry is already mapped with the right
          		 * attributes, or already absent in the case of
          		 * unmapping, no need to do anything; carry on to the
          		 * next entry.
          		 */
          	} else if ((end - begin) >= entry_size &&
          		   (unmap || arch_mm_is_block_allowed(level)) &&
          		   (begin & (entry_size - 1)) == 0) {
          		/*
          		 * If the entire entry is within the region we want to
          		 * map, map/unmap the whole entry.
          		 */
          		if (commit) {
          			pte_t new_pte =
          				unmap ? arch_mm_absent_pte(level)
          				      : arch_mm_block_pte(level, pa,
          							  attrs);
          			mm_replace_entry(begin, pte, new_pte, level,
          					 flags, ppool);
          		}
          	} else {
          		/*
          		 * If the entry is already a subtable get it; otherwise
          		 * replace it with an equivalent subtable and get that.
          		 */
          		struct mm_page_table *nt = mm_populate_table_pte(
          			begin, pte, level, flags, ppool);
          		if (nt == NULL) {
          			return false;
          		}
   
          		/*
          		 * Recurse to map/unmap the appropriate entries within
          		 * the subtable.
          		 */
          		if (!mm_map_level(begin, end, pa, attrs, nt, level - 1,
          				  flags, ppool)) {
          			return false;
          		}
          	}
   
          	begin = mm_start_of_next_block(begin, entry_size);
          	pa = mm_pa_start_of_next_block(pa, entry_size);
          	pte++;
          }
   
          return true;
  }
   *)

  Definition mm_map_level (a_begin a_end pa attrs table level flags ppool n: var) 
             (pte level_end entry_size commit unmap new_pte nt cond: var) :=
    (* XXX: How can we handle this aliasing? *)
    pte #= (load_at_i table (unsigned (expr_to_int (Call "MM.mm_index" [CBV a_begin; CBV level])))) #;
        level_end #= (Call "MM.mm_level_end" [CBV a_begin; CBV level]) #;
        entry_size #= (Call "MM.mm_entry_size" [CBV level]) #;
        commit #= (flags #& MM_FLAG_COMMIT) #;
        unmap #= (flags #& MM_FLAG_UNMAP) #;
        (#if (level_end < a_end)
          then a_end #= level_end
          else Skip) #;
        #while (a_begin < a_end)
        do (
            (* XXX: Need to check the precedence of each operator - e.g. == ? && ? *)
            (* move this condition due to our syntax *)
            (#if (unmap)
              then cond #= (#! (Call "ARCHMM.arch_mm_pte_is_present" [CBR pte; CBV level]))
              else cond #= ((Call "ARCHMM.arch_mm_pte_is_block" [CBR pte; CBV level])
                              #&& ((Call "ARCHMM.arch_mm_pte_attrs" [CBR pte; CBV level]) == attrs)))
              #;
                            
            (#if (cond)
              then Skip
              else (#if ((entry_size <= (a_end - a_begin))
                           #&& (unmap #|| (Call "ARCHMM.arch_mm_is_block_allowed" [CBV level]))
                           #&& (a_begin #& (entry_size - one) == zero))
                     then (#if (commit)
                            then (#if (unmap)
                                   then new_pte #= (Call "ARCHMM.arch_mm_absent_pte" [CBV level])
                                   else new_pte #= (Call "ARCHMM.arch_mm_block_pte" [CBV level; CBV pa; CBV attrs]))
                                   #;
                                   (Call "MM.mm_replace_entry" [CBV a_begin; CBR pte; CBR new_pte; CBV level;
                                                               CBV flags; CBR ppool])
                            else Skip)
                     else nt #= (Call "MM.mm_populate_table_pte" [CBV a_begin; CBR pte; CBV level; CBV flags; CBR ppool]) #;
                             (#if (nt == Vnull)
                               then Return Vfalse
                               else Skip) #;
                             (#if (#! (Call "MM.mm_map_level" [CBV a_begin; CBV a_end; CBV pa; CBV attrs; CBR nt;
                                                              CBV (level - one); CBV flags; CBR ppool]))
                               then Return Vfalse
                               else Skip) #;
                             a_begin #= (Call "MM.mm_start_of_next_block" [CBV a_begin; CBV entry_size]) #;
                             pa #= (Call "MM.mm_pa_start_of_next_block" [CBV pa; CBV entry_size]) #;
                             pte #= (Cast ((Cast pte tint) + one) tptr)))
          ) #;
            Return Vtrue.
  
  (*
  /**
   * Updates the page table from the root to map the given address range to a
   * physical range using the provided (architecture-specific) attributes. Or if
   * MM_FLAG_UNMAP is set, unmap the given range instead.
   */
  static bool mm_map_root(struct mm_ptable *t, ptable_addr_t begin,
          		ptable_addr_t end, uint64_t attrs, uint8_t root_level,
          		int flags, struct mpool *ppool)
  {
          size_t root_table_size = mm_entry_size(root_level);
          struct mm_page_table *table =
          	&mm_page_table_from_pa(t->root)[mm_index(begin, root_level)];
   
          while (begin < end) {
          	if (!mm_map_level(begin, end, pa_init(begin), attrs, table,
          			  root_level - 1, flags, ppool)) {
          		return false;
          	}
          	begin = mm_start_of_next_block(begin, root_table_size);
          	table++;
          }
   
          return true;
  }
   *)

   Definition mm_map_root (t a_begin a_end attrs root_level flags ppool : var)
              (root_table_size table mm_ptable mm_index: var) := 
     root_table_size #= (Call "MM.mm_entry_size" [CBV root_level]) #;
                     (* XXX: need to think about this alaising *)
                     mm_ptable #= (Call "MM.mm_page_table_from_pa" [CBV (load_at_i t root_loc)]) #;
                     mm_index #= (Call "MM.mm_index" [CBV a_begin; CBV root_level]) #;
                     table #= (load_at_i mm_ptable (unsigned (expr_to_int (Var mm_index)))) #;
                     #while (a_begin < a_end)
                     do (
                         (#if (#! (Call "MM.mm_map_level" [CBV a_begin; CBV a_end;
                                                          CBV (Call "ADDR.pa_init" [CBV a_begin]);
                                                          CBV attrs; CBR table; CBV (root_level - one);
                                                          CBV flags; CBR ppool]))
                           then Return Vfalse
                           else Skip)
                           #;
                           a_begin #= (Call "MM.mm_start_of_next_block" [CBV a_begin; CBV root_table_size]) #;
                           table #= (Cast ((Cast table tint) + one) tptr)
                       ) #;
                         Return Vtrue.
  
  (*
  /**
   * Updates the given table such that the given physical address range is mapped
   * or not mapped into the address space with the architecture-agnostic mode
   * provided. Only commits the change if MM_FLAG_COMMIT is set.
   */
  static bool mm_ptable_identity_map(struct mm_ptable *t, paddr_t pa_begin,
          			   paddr_t pa_end, uint64_t attrs, int flags,
          			   struct mpool *ppool)
  {
          uint8_t root_level = mm_max_level(flags) + 1;
          ptable_addr_t ptable_end = mm_ptable_addr_space_end(flags);
          ptable_addr_t end = mm_round_up_to_page(pa_addr(pa_end));
          ptable_addr_t begin = pa_addr(arch_mm_clear_pa(pa_begin));
   
          /*
           * Assert condition to communicate the API constraint of mm_max_level(),
           * that isn't encoded in the types, to the static analyzer.
           */
          CHECK(root_level >= 2);
   
          /* Cap end to stay within the bounds of the page table. */
          if (end > ptable_end) {
          	end = ptable_end;
          }
   
          if (!mm_map_root(t, begin, end, attrs, root_level, flags, ppool)) {
          	return false;
          }
   
          /* Invalidate the TLB. */
          if ((flags & MM_FLAG_COMMIT) &&
              ((flags & MM_FLAG_STAGE1) || mm_stage2_invalidate)) {
          	mm_invalidate_tlb(begin, end, flags);
          }
   
          return true;
  }
   *)

  Definition  mm_ptable_identity_map (t pa_begin pa_end attrs flags ppool : var) (root_level ptable_end a_end a_begin: var) :=
    root_level #= ((Call "MM.mm_max_level" [CBV flags]) + one) #;
               ptable_end #= (Call "MM.mm_ptable_addr_space_end" [CBV flags]) #;
               a_end #= (Call "MM.mm_round_up_to_page" [CBV (Call "ADDR.pa_addr" [CBV pa_end])]) #;
               a_begin #= (Call "ADDR.pa_addr" [CBV (Call "ARCHMM.arch_mm_clear_pa" [CBV pa_begin])]) #;
               (* XXX: Need to add the following condition 
               CHECK(root_level >= 2); *)
               (#if (ptable_end < a_end)
                 then a_end #= ptable_end
                 else Skip) #;
               (#if (#! (Call "MM.mm_map_root" [CBV t; CBV a_begin; CBV a_end; CBV attrs; CBV root_level;
                                               CBV flags; CBR ppool]))
                 then Return Vfalse
                 else Skip) #;
               (#if ((flags #& MM_FLAG_COMMIT)
                       #&& ((flags #& MM_FLAG_STAGE1) #|| mm_stage2_invalidate))
                 then (Call "MM.mm_invalidate_tlb" [CBV a_begin; CBV a_end; CBV flags])
                 else Skip) #;
               Return Vtrue.
  
  (*
  /*
   * Prepares the given page table for the given address mapping such that it
   * will be able to commit the change without failure. It does so by ensuring
   * the smallest granularity needed is available. This remains valid provided
   * subsequent operations no not decrease the granularity.
   *
   * In particular, multiple calls to this function will result in the
   * corresponding calls to commit the changes to succeed.
   */
  static bool mm_ptable_identity_prepare(struct mm_ptable *t, paddr_t pa_begin,
          			       paddr_t pa_end, uint64_t attrs,
          			       int flags, struct mpool *ppool)
  {
          flags &= ~MM_FLAG_COMMIT;
          return mm_ptable_identity_map(t, pa_begin, pa_end, attrs, flags, ppool);
  }
  *)

  Definition  mm_ptable_identity_prepare (t pa_begin pa_end attrs flags ppool: var) :=
    flags #= flags #& (#~ MM_FLAG_COMMIT) #;
          Return (Call "MM.mm_ptable_identity_map" [CBR t; CBV pa_begin; CBV pa_end; CBV attrs; CBV flags; CBR ppool]).


  (* XXX: The following function is only for checking *)
  (*
  /**
   * Commits the given address mapping to the page table assuming the operation
   * cannot fail. `mm_ptable_identity_prepare` must used correctly before this to
   * ensure this condition.
   *
   * Without the table being properly prepared, the commit may only partially
   * complete if it runs out of memory resulting in an inconsistent state that
   * isn't handled.
   *
   * Since the non-failure assumtion is used in the reasoning about the atomicity
   * of higher level memory operations, any detected violations result in a panic.
   *
   * TODO: remove ppool argument to be sure no changes are made.
   */
  static void mm_ptable_identity_commit(struct mm_ptable *t, paddr_t pa_begin,
          			      paddr_t pa_end, uint64_t attrs, int flags,
          			      struct mpool *ppool)
  {
          CHECK(mm_ptable_identity_map(t, pa_begin, pa_end, attrs,
          			     flags | MM_FLAG_COMMIT, ppool));
  }
   


  /**
   * Updates the given table such that the given physical address range is mapped
   * or not mapped into the address space with the architecture-agnostic mode
   * provided.
   *
   * The page table is updated using the separate prepare and commit stages so
   * that, on failure, a partial update of the address space cannot happen. The
   * table may be left with extra internal tables but the address space is
   * unchanged.
   */
  static bool mm_ptable_identity_update(struct mm_ptable *t, paddr_t pa_begin,
          			      paddr_t pa_end, uint64_t attrs, int flags,
          			      struct mpool *ppool)
  {
          if (!mm_ptable_identity_prepare(t, pa_begin, pa_end, attrs, flags,
          				ppool)) {
          	return false;
          }
   
          mm_ptable_identity_commit(t, pa_begin, pa_end, attrs, flags, ppool);
   
          return true;
  }
   *)

  Definition mm_ptable_identity_update (t pa_begin pa_end attrs flags ppool : var) :=
    (#if (#! (Call "MM.mm_ptable_identity_prepare" [CBR t; CBV pa_begin; CBV pa_end; CBV attrs; CBV flags; CBR ppool]))
     then Return Vfalse
     else Skip) #;
     (* XXX: Need to make the folloinwg condition as a safety check 
        mm_ptable_identity_commit(t, pa_begin, pa_end, attrs, flags, ppool); *) 
                Return Vtrue.
   
  (* XXX: ignoring the following function - its for logging 
  //JIEUNG: ignore following two functions
  /**
   * Writes the given table to the debug log, calling itself recursively to
   * write sub-tables.
   */
  static void mm_dump_table_recursive(struct mm_page_table *table, uint8_t level,
          			    int max_level)
  {
          uint64_t i;
   
          for (i = 0; i < MM_PTE_PER_PAGE; i++) {
          	if (!arch_mm_pte_is_present(table->entries[i], level)) {
          		continue;
          	}
   
          	dlog("%*s%x: %x\n", 4 * (max_level - level), "", i,
          	     table->entries[i]);
   
          	if (arch_mm_pte_is_table(table->entries[i], level)) {
          		mm_dump_table_recursive(
          			mm_page_table_from_pa(arch_mm_table_from_pte(
          				table->entries[i], level)),
          			level - 1, max_level);
          	}
          }
  }
  *)   

  (* XXX: ignoring the following function - its for logging 
  /**
   * Writes the given table to the debug log.
   */
  static void mm_ptable_dump(struct mm_ptable *t, int flags)
  {
          struct mm_page_table *tables = mm_page_table_from_pa(t->root);
          uint8_t max_level = mm_max_level(flags);
          uint8_t root_table_count = mm_root_table_count(flags);
          uint8_t i;
   
          for (i = 0; i < root_table_count; ++i) {
          	mm_dump_table_recursive(&tables[i], max_level, max_level);
          }
  }
   *)
   

  (* 
  /**
   * Given the table PTE entries all have identical attributes, returns the single
   * entry with which it can be replaced. Note that the table PTE will no longer
   * be valid after calling this function as the table may have been freed.
   *
   * If the table is freed, the memory is freed directly rather than calling
   * `mm_free_page_pte()` as it is known to not have subtables.
   */
  static pte_t mm_merge_table_pte(pte_t table_pte, uint8_t level,
          			struct mpool *ppool)
  {
          struct mm_page_table *table;
          uint64_t block_attrs;
          uint64_t table_attrs;
          uint64_t combined_attrs;
          paddr_t block_address;
   
          table = mm_page_table_from_pa(arch_mm_table_from_pte(table_pte, level));
   
          if (!arch_mm_pte_is_present(table->entries[0], level - 1)) {
          	/* Free the table and return an absent entry. */
          	mpool_free(ppool, table);
          	return arch_mm_absent_pte(level);
          }
   
          /* Might not be possible to merge the table into a single block. */
          if (!arch_mm_is_block_allowed(level)) {
          	return table_pte;
          }
   
          /* Replace table with a single block, with equivalent attributes. */
          block_attrs = arch_mm_pte_attrs(table->entries[0], level - 1);
          table_attrs = arch_mm_pte_attrs(table_pte, level);
          combined_attrs =
          	arch_mm_combine_table_entry_attrs(table_attrs, block_attrs);
          block_address = arch_mm_block_from_pte(table->entries[0], level - 1);
   
          /* Free the table and return a block. */
          mpool_free(ppool, table);
          return arch_mm_block_pte(level, block_address, combined_attrs);
  }
   *)

  Definition mm_merge_table_pte (table_pte level ppool : var)
             (table block_attrs table_attrs combined_attrs block_address : var) :=
    table #= (Call "MM.mm_page_table_from_pa" [CBV (Call "ARCHMM.arch_mm_table_from_pte" [CBR table_pte; CBV level])]) #;
          (#if (#! (Call "ARCHMM.arch_mm_pte_is_present" [CBV (load_at_i table 0); CBV (level - one)]))
            then (Call "MPOOL.mpool_free" [CBR ppool; CBR table])
                   #;
                   Return (Call "ARCHMM.arch_mm_absent_pte" [CBV level])
            else Skip) #;
          (#if (#! (Call "ARCHMM.arch_mm_is_block_allowed" [CBV level]))
            then Return table_pte
            else Skip) #;
          block_attrs #= (Call "ARCHMM.arch_mm_pte_attrs" [CBV (load_at_i table 0); CBV (level - one)]) #;
          table_attrs #= (Call "ARCHMM.arch_mm_pte_attrs" [CBV table_pte; CBV level]) #;
          combined_attrs #= (Call "ARCHMM.arch_mm_combine_table_entry_attrs" [CBV table_attrs; CBV block_attrs]) #;
          block_address #= (Call "ARCHMM.arch_mm_block_from_pte" [CBV (load_at_i table 0); CBV (level - one)]) #;
          (Call "MPOOL.mpool_free" [CBR ppool; CBR table]) #;
          Return (Call "ARCHMM.arch_mm_block_pte" [CBV level; CBV block_address; CBV combined_attrs]).
  
  (*
  // JIEUNG: need to be included as our target
  /**
   * Defragments the given PTE by recursively replacing any tables with blocks or
   * absent entries where possible.
   */
  static pte_t mm_ptable_defrag_entry(pte_t entry, uint8_t level,
          			    struct mpool *ppool)
  {
          struct mm_page_table *table;
          uint64_t i;
          bool mergeable;
          bool base_present;
          uint64_t base_attrs;
   
          if (!arch_mm_pte_is_table(entry, level)) {
          	return entry;
          }
   
          table = mm_page_table_from_pa(arch_mm_table_from_pte(entry, level));
   
          /* Defrag the first entry in the table and use it as the base entry. */
          static_assert(MM_PTE_PER_PAGE >= 1, "There must be at least one PTE.");
          table->entries[0] =
          	mm_ptable_defrag_entry(table->entries[0], level - 1, ppool);
          base_present = arch_mm_pte_is_present(table->entries[0], level - 1);
          base_attrs = arch_mm_pte_attrs(table->entries[0], level - 1);
   
          /*
           * Defrag the remaining entries in the table and check whether they are
           * compatible with the base entry meaning the table can be merged into a
           * block entry. It assumes addresses are contiguous due to identity
           * mapping.
           */
          mergeable = true;
          for (i = 1; i < MM_PTE_PER_PAGE; ++i) {
          	bool present;
   
          	table->entries[i] = mm_ptable_defrag_entry(table->entries[i],
          						   level - 1, ppool);
          	present = arch_mm_pte_is_present(table->entries[i], level - 1);
   
          	if (present != base_present) {
          		mergeable = false;
          		continue;
          	}
   
          	if (!present) {
          		continue;
          	}
   
          	if (!arch_mm_pte_is_block(table->entries[i], level - 1)) {
          		mergeable = false;
          		continue;
          	}
   
          	if (arch_mm_pte_attrs(table->entries[i], level - 1) !=
          	    base_attrs) {
          		mergeable = false;
          		continue;
          	}
          }
   
          if (mergeable) {
          	return mm_merge_table_pte(entry, level, ppool);
          }
   
          return entry;
  }
   *)


  Definition mm_ptable_defrag_entry (entry level ppool : var) (table i mergeable base_present base_attrs i present : var) :=
    (#if (#! (Call "ARCHMM.arch_mm_pte_is_table" [CBV entry; CBV level]))
      then Return entry
      else Skip)
      #;
      table #= (Call "MM.mm_page_table_from_pa" [CBV (Call "ARCHMM.arch_mm_table_from_pte" [CBV entry; CBV level])]) #;
      (* XXX: Need to add the following condition as an assertion 
      static_assert(MM_PTE_PER_PAGE >= 1, "There must be at least one PTE."); *)
      (store_at_i table 0 (Call "MM.mm_ptable_defrag_entry" [CBV (load_at_i table 0); CBV (level - one); CBR ppool])) #;
      base_present #= (Call "ARCHMM.arch_mm_pte_is_present" [CBV (load_at_i table 0); CBV (level - one)]) #;
      base_attrs #= (Call "ARCHMM.arch_mm_pte_attrs" [CBV (load_at_i table 0); CBV (level - one)]) #;
      mergeable #= Vtrue #;
      i #= zero #;
      #while (i < MM_PTE_PER_PAGE)
      do (
          (store_at_i table (unsigned (expr_to_int (Var i)))
                      (Call "MM.mm_ptable_defrag_entry" [CBV (load_at_i table (unsigned (expr_to_int (Var i))));
                                                        CBV (level - one); CBR ppool]))
            #;
            present #= (Call "ARCHMM.arch_mm_pte_is_present" [CBV (load_at_i table (unsigned (expr_to_int (Var i))));
                                                             CBV (level - one)]) #;
            (* XXX: refactoring that one due to continue *)
            (#if (#! (present == base_present))
              then mergeable #= Vfalse
              else (#if (#! present)
                     then Skip
                     else (#if (#! (Call "ARCHMM.arch_mm_pte_is_block"
                                         [CBV (load_at_i table (unsigned (expr_to_int (Var i))));
                                         CBV (level - one)]))
                            then mergeable #= Vfalse
                            else (#if (#! ((Call "ARCHMM.arch_mm_pte_attrs"
                                                [CBV (load_at_i table (unsigned (expr_to_int (Var i))));
                                                CBV (level - one)]) == base_attrs))
                                   then mergeable #= Vfalse
                                   else Skip)))) #;
            i #= i + one
        ) #;
          (#if (mergeable)
            then Return (Call "MM.mm_merge_table_pte" [CBV entry; CBV level; CBR ppool])
            else Skip) #;
          Return entry.
  
  (* 
  /**
   * Defragments the given page table by converting page table references to
   * blocks whenever possible.
   */
  static void mm_ptable_defrag(struct mm_ptable *t, int flags,
          		     struct mpool *ppool)
  {
          struct mm_page_table *tables = mm_page_table_from_pa(t->root);
          uint8_t level = mm_max_level(flags);
          uint8_t root_table_count = mm_root_table_count(flags);
          uint8_t i;
          uint64_t j;
   
          /*
           * Loop through each entry in the table. If it points to another table,
           * check if that table can be replaced by a block or an absent entry.
           */
          for (i = 0; i < root_table_count; ++i) {
          	for (j = 0; j < MM_PTE_PER_PAGE; ++j) {
          		tables[i].entries[j] = mm_ptable_defrag_entry(
          			tables[i].entries[j], level, ppool);
          	}
          }
  }
   *)

  Definition mm_ptable_defrag (t flags ppool : var) (tables level root_table_count i j : var):=
    tables #= (Call "MM.mm_page_table_from_pa" [CBV (load_at_i t root_loc)]) #;
           level #= (Call "MM.mm_max_level" [CBV flags]) #;
           root_table_count #= (Call "MM.mm_root_table_count" [CBV flags]) #;
           i #= zero #;
           #while (i < root_table_count)
           do (
               j #= zero #;
                 #while (j < MM_PTE_PER_PAGE)
                 do (
                     (store_at_i tables ((unsigned (expr_to_int (Var i))) * entries_size +
                                         (unsigned (expr_to_int (Var j))))
                                 (Call "MM.mm_ptable_defrag_entries"
                                       [CBV (load_at_i tables
                                                       ((unsigned (expr_to_int (Var i))) * entries_size +
                                                        (unsigned (expr_to_int (Var j)))));
                                       CBV level; CBR ppool]))
                       #;
                       j #= j + one 
                   )  #;
               i #= i + one 
             ).
  
  (*
  /**
   * Gets the attributes applied to the given range of stage-2 addresses at the
   * given level.
   *
   * The `got_attrs` argument is initially passed as false until `attrs` contains
   * attributes of the memory region at which point it is passed as true.
   *
   * The value returned in `attrs` is only valid if the function returns true.
   *
   * Returns true if the whole range has the same attributes and false otherwise.
   */
  static bool mm_ptable_get_attrs_level(struct mm_page_table *table,
          			      ptable_addr_t begin, ptable_addr_t end,
          			      uint8_t level, bool got_attrs,
          			      uint64_t *attrs)
  {
          pte_t *pte = &table->entries[mm_index(begin, level)];
          ptable_addr_t level_end = mm_level_end(begin, level);
          size_t entry_size = mm_entry_size(level);
   
          /* Cap end so that we don't go over the current level max. */
          if (end > level_end) {
          	end = level_end;
          }
   
          /* Check that each entry is owned. */
          while (begin < end) {
          	if (arch_mm_pte_is_table( *pte, level)) {
          		if (!mm_ptable_get_attrs_level(
          			    mm_page_table_from_pa(
          				    arch_mm_table_from_pte( *pte,
          							   level)),
          			    begin, end, level - 1, got_attrs, attrs)) {
          			return false;
          		}
          		got_attrs = true;
          	} else {
          		if (!got_attrs) {
          			*attrs = arch_mm_pte_attrs( *pte, level);
          			got_attrs = true;
          		} else if (arch_mm_pte_attrs( *pte, level) != *attrs) {
          			return false;
          		}
          	}
   
          	begin = mm_start_of_next_block(begin, entry_size);
          	pte++;
          }
   
          /* The entry is a valid block. */
          return got_attrs;
  }
  *)

  Definition mm_ptable_get_attrs_level (table a_begin a_end level got_attrs attrs: var) 
             (pte level_end entry_size : var) :=
    (* XXX: How can we handle this aliasing? *)
    pte #= (load_at_i table (unsigned (expr_to_int (Call "MM.mm_index" [CBV a_begin; CBV level])))) #;
        level_end #= (Call "MM.mm_level_end" [CBV a_begin; CBV level]) #;
        entry_size #= (Call "MM.mm_entry_size" [CBV level]) #;
        (#if (level_end < a_end)
          then a_end #= level_end
          else Skip) #;
        #while (a_begin < a_end)
        do (
            (#if (Call "ARCHMM.arch_mm_pte_is_table" [CBR pte; CBV level])
              then (#if (#! (Call "MM.mm_ptable_get_attrs_level"
                                  [CBV (Call "MM.mm_ptable_from_pa"
                                             [CBV (Call "ARCHMM.arch_mm_table_from_pte" [CBR pte; CBV level])]);
                                  CBV a_begin; CBV a_end; CBV (level - one); CBV got_attrs; CBV attrs]))
                     then Return Vfalse
                     else Skip)
              else (#if (#! got_attrs)
                     then attrs #= (Call "ARCHMM.arch_mm_pte_attrs" [CBR pte; CBV level]) #;
                                got_attrs #= Vtrue
                     else (#if (#! ((Call "ARCHMM.arch_mm_pte_attrs" [CBR pte; CBV level]) == attrs))
                            then Return Vfalse
                            else Skip)))
              #;
              a_begin #= (Call "MM.mm_start_of_next_block" [CBV a_begin; CBV entry_size]) #;
              pte #= (Cast ((Cast pte tint) + one) tptr)
          ) #;
            Return got_attrs.
  
  (*
  /**
   * Gets the attributes applies to the given range of addresses in the stage-2
   * table.
   *
   * The value returned in `attrs` is only valid if the function returns true.
   *
   * Returns true if the whole range has the same attributes and false otherwise.
   */
  static bool mm_vm_get_attrs(struct mm_ptable *t, ptable_addr_t begin,
          		    ptable_addr_t end, uint64_t *attrs)
  {
          int flags = 0;
          uint8_t max_level = mm_max_level(flags);
          uint8_t root_level = max_level + 1;
          size_t root_table_size = mm_entry_size(root_level);
          ptable_addr_t ptable_end =
          	mm_root_table_count(flags) * mm_entry_size(root_level);
          struct mm_page_table *table;
          bool got_attrs = false;
   
          begin = mm_round_down_to_page(begin);
          end = mm_round_up_to_page(end);
   
          /* Fail if the addresses are out of range. */
          if (end > ptable_end) {
          	return false;
          }
   
          table = &mm_page_table_from_pa(t->root)[mm_index(begin, root_level)];
          while (begin < end) {
          	if (!mm_ptable_get_attrs_level(table, begin, end, max_level,
          				       got_attrs, attrs)) {
          		return false;
          	}
   
          	got_attrs = true;
          	begin = mm_start_of_next_block(begin, root_table_size);
          	table++;
          }
   
          return got_attrs;
  }
  *)

  Definition mm_vm_get_attrs (t a_begin a_end attrs: var)            
             (flags max_level root_level root_table_size ptable_end table got_attrs mm_ptable mm_index : var) :=
    flags #= zero #;
          max_level #= (Call "MM.mm_max_level" [CBV flags]) #;
          root_level #= (max_level + one) #;
          root_table_size #= (Call "MM.mm_entry_size" [CBV root_level]) #;
          ptable_end #= ((Call "MM.mm_root_table_count" [CBV flags]) *
                         (Call "MM.mm_entry_size" [CBV root_level])) #;
          got_attrs #= Vfalse #;
          a_begin #= (Call "MM.mm_round_down_to_page" [CBV a_begin]) #;
          a_end #= (Call "MM.mm_round_up_to_page" [CBV a_end]) #;
          (#if (ptable_end < a_end)
            then Return Vfalse
            else Skip) #;
          (* XXX: How can we handle this alaising? *)
          mm_ptable #= (Call "MM.mm_page_table_from_pa" [CBV (load_at_i t root_loc)]) #;
          mm_index #= (Call "MM.mm_index" [CBV a_begin; CBV root_level]) #;
          table #= (load_at_i mm_ptable (unsigned (expr_to_int (Var mm_index)))) #;
          #while (a_begin < a_end)
          do (
              (#if (#! (Call "MM.mm_ptable_get_attrs_level"
                             [CBR table; CBV a_begin; CBV a_end; CBV max_level; CBV got_attrs; CBV attrs]))
                then Return Vfalse
                else Skip)
                #;
                got_attrs #= Vtrue #;
                a_begin #= (Call "MM.mm_start_of_next_block" [CBV a_begin; CBV root_table_size]) #;
                table #= (Cast ((Cast table tint) + one) tptr) 
            ) #;
              Return got_attrs.

  (*
  bool mm_vm_init(struct mm_ptable *t, struct mpool *ppool)
  {
          return mm_ptable_init(t, 0, ppool);
  }
   *)

  Definition  mm_vm_init (t ppool : var) :=
    Return (Call "MM.mm_ptable_init" [CBR t; CBV zero; CBR ppool]).

  (*
  void mm_vm_fini(struct mm_ptable *t, struct mpool *ppool)
  {
          mm_ptable_fini(t, 0, ppool);
  }
  *)

  Definition  mm_vm_fini (t ppool : var) :=
    Return (Call "MM.mm_ptable_fini" [CBR t; CBV zero; CBR ppool]).

  
  (*
  /**
   * Selects flags to pass to the page table manipulation operation based on the
   * mapping mode.
   */
  static int mm_mode_to_flags(uint32_t mode)
  {
          if ((mode & MM_MODE_UNMAPPED_MASK) == MM_MODE_UNMAPPED_MASK) {
          	return MM_FLAG_UNMAP;
          }
   
          return 0;
  }
   *)

  Definition  mm_mode_to_flags (mode : var) :=
    #if ((mode #& MM_MODE_UNMAPPED_MASK) == MM_MODE_UNMAPPED_MASK)
     then Return MM_FLAG_UNMAP
     else Return zero.

  (*
  /**
   * See `mm_ptable_identity_prepare`.
   *
   * This must be called before `mm_vm_identity_commit` for the same mapping.
   *
   * Returns true on success, or false if the update would fail.
   */
  bool mm_vm_identity_prepare(struct mm_ptable *t, paddr_t begin, paddr_t end,
          		    uint32_t mode, struct mpool *ppool)
  {
          int flags = mm_mode_to_flags(mode);
   
          return mm_ptable_identity_prepare(t, begin, end,
          				  arch_mm_mode_to_stage2_attrs(mode),
          				  flags, ppool);
  }
   *)

  Definition mm_vm_identity_prepare (t a_begin a_end mode ppool : var) (flags : var):=
    flags #= (Call "MM.mm_mode_to_flags" [CBV mode]) #;
          Return (Call "MM.mm_ptable_identity_prepare" [CBR t; CBV a_begin; CBV a_end;
                                                       CBV (Call "ARCHMM.arch_mm_to_stage2_attrs" [CBV mode]);
                                                       CBV flags; CBR ppool]).
 
  (* 
  /**
   * See `mm_ptable_identity_commit`.
   *
   * `mm_vm_identity_prepare` must be called before this for the same mapping.
   */
  void mm_vm_identity_commit(struct mm_ptable *t, paddr_t begin, paddr_t end,
          		   uint32_t mode, struct mpool *ppool, ipaddr_t *ipa)
  {
          int flags = mm_mode_to_flags(mode);
   
          mm_ptable_identity_commit(t, begin, end,
          			  arch_mm_mode_to_stage2_attrs(mode), flags,
          			  ppool);
   
          if (ipa != NULL) {
          	*ipa = ipa_from_pa(begin);
          }
  }
   *)

  Definition mm_vm_identity_commit (t a_begin a_end mode ppool ipa: var) (flags : var) :=
    flags #= (Call "MM.mm_mode_to_flags" [CBV mode]) #;
          (Call "MM.mm_ptable_identity_commit" [CBR t; CBV a_begin; CBV a_end;
                                               CBV (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode]);
                                               CBV flags; CBR ppool]) #;
          #if (#! (ipa == Vnull))
           then ipa #= (Call "ADDR.ipa_from_pa" [CBV a_begin])
           else Skip.                 
                   
  (*
  /**
   * Updates a VM's page table such that the given physical address range is
   * mapped in the address space at the corresponding address range in the
   * architecture-agnostic mode provided.
   *
   * mm_vm_defrag should always be called after a series of page table updates,
   * whether they succeed or fail. This is because on failure extra page table
   * entries may have been allocated and then not used, while on success it may be
   * possible to compact the page table by merging several entries into a block.
   *
   * Returns true on success, or false if the update failed and no changes were
   * made.
   */
  bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
          		uint32_t mode, struct mpool *ppool, ipaddr_t *ipa)
  {
          int flags = mm_mode_to_flags(mode);
          bool success = mm_ptable_identity_update(
          	t, begin, end, arch_mm_mode_to_stage2_attrs(mode), flags,
          	ppool);
   
          if (success && ipa != NULL) {
          	*ipa = ipa_from_pa(begin);
          }
   
          return success;
  }
  *)
   

  Definition mm_vm_identity_map (t a_begin a_end mode ppool ipa : var) (flags success : var) :=
    flags #= (Call "MM.mm_mode_to_flags" [CBV mode]) #;
          success #= (Call "MM.mm_ptable_identity_update" [CBR t; CBV a_begin; CBV a_end;
                                                          CBV (Call "MM.arch_mm_mode_to_stage2_attrs" [CBV mode]);
                                                          CBV flags; CBR ppool]) #;
          (#if (success #&& (#! (ipa == Vnull)))
            then ipa #= (Call "ADDR.ipa_from_pa" [CBV a_begin])
            else Skip) #;
          Return success.
  (*
  /**
   * Updates the VM's table such that the given physical address range has no
   * connection to the VM.
   */
  bool mm_vm_unmap(struct mm_ptable *t, paddr_t begin, paddr_t end,
          	 struct mpool *ppool)
  {
          uint32_t mode = MM_MODE_UNMAPPED_MASK;
   
          return mm_vm_identity_map(t, begin, end, mode, ppool, NULL);
  }
  *)

  Definition mm_vm_unmap (t a_begin a_end ppool : var) (mode : var):=
    mode #= MM_MODE_UNMAPPED_MASK #;
         Return (Call "MM.mm_vm_identity_map" [CBR t; CBV a_begin; CBV a_end; CBV mode; CBR ppool; CBV Vnull]).
  
  (*
  /**
   * Write the given page table of a VM to the debug log.
   */
  void mm_vm_dump(struct mm_ptable *t)
  {
          mm_ptable_dump(t, 0);
  }
   *)

  Definition mm_vm_dump (t: var) :=
    (Call "MM.mm_ptable_dump" [CBR t; CBV zero]). 

  (*
  /**
   * Defragments the VM page table.
   */
  void mm_vm_defrag(struct mm_ptable *t, struct mpool *ppool)
  {
          mm_ptable_defrag(t, 0, ppool);
  }
   *)

  Definition mm_vm_defrag (t ppool : var) :=
    (Call "MM.mm_ptable_defrag" [CBR t; CBV zero; CBR ppool]).
   
  (*
  /**
   * Gets the mode of the give range of intermediate physical addresses if they
   * are mapped with the same mode.
   *
   * Returns true if the range is mapped with the same mode and false otherwise.
   */
  bool mm_vm_get_mode(struct mm_ptable *t, ipaddr_t begin, ipaddr_t end,
          	    uint32_t *mode)
  {
          uint64_t attrs;
          bool ret;
   
          ret = mm_vm_get_attrs(t, ipa_addr(begin), ipa_addr(end), &attrs);
          if (ret) {
          	*mode = arch_mm_stage2_attrs_to_mode(attrs);
          }
   
          return ret;
  }
  *)

  Definition  mm_vm_get_mode (t a_begin a_end mode: var) (attrs ret : var) :=
    (* XXX: is passing attrs ok? *)
    ret #= (Call "MM.mm_vm_get_attrs" [CBR t; CBV (Call "ADDR.ipa_addr" [CBV a_begin]);
                                      CBV (Call "ADDR.ipa_addr" [CBV a_end]);
                                      CBR attrs]) #;
        (#if (ret)
          then mode #= (Call "ARCHMM.arch_mm_stage2_attrs_to_mode" [CBV attrs])
          else Skip) #;
        Return ret.


  (* XXX: What is the purpose of this one. We need to check the following things *) 
  (*
  static struct mm_stage1_locked mm_stage1_lock_unsafe(void)
  {
          return (struct mm_stage1_locked){.ptable = &ptable};
  }
   *)

  Definition mm_stage1_lock_unsafe (res : var):=
    (store_at_i res ptable_loc (Cast ptable tint)) #; Return res.

  (*
  struct mm_stage1_locked mm_lock_stage1(void)
  {
          sl_lock(&ptable_lock);
          return mm_stage1_lock_unsafe();
  }
  *)

  
  Definition mm_lock_stage1 (p : var) :=
    (Call "Lock.acquire" [CBV (load_at_i ptable_lock 0) ; CBV ptable_lock]) #;
      Return (Call "MM.mm_stage1_locked" []).

  
  (*
  void mm_unlock_stage1(struct mm_stage1_locked *lock)
  {
          CHECK(lock->ptable == &ptable);
          sl_unlock(&ptable_lock);
          lock->ptable = NULL;
  }
  *)

  Definition mm_unlock_stage1 (lock : var) :=
    (* XXX: add safety condition in here 
          CHECK(lock->ptable == &ptable); *)
    (Call "Lock.release" [CBV (load_at_i ptable_lock 0) ; CBV ptable_lock]) #; (store_at_i lock ptable_loc Vnull).

  (* 
  /**
   * Updates the hypervisor page table such that the given physical address range
   * is mapped into the address space at the corresponding address range in the
   * architecture-agnostic mode provided.
   */
  void *mm_identity_map(struct mm_stage1_locked stage1_locked, paddr_t begin,
          	      paddr_t end, uint32_t mode, struct mpool *ppool)
  {
          int flags = MM_FLAG_STAGE1 | mm_mode_to_flags(mode);
   
          if (mm_ptable_identity_update(stage1_locked.ptable, begin, end,
          			      arch_mm_mode_to_stage1_attrs(mode), flags,
          			      ppool)) {
          	return ptr_from_va(va_from_pa(begin));
          }
   
          return NULL;
  }
   *)

  Definition mm_identity_map (stage1_locked a_begin a_end mode ppool: var) (flags : var):=
    flags #= (MM_FLAG_STAGE1 #| (Call "MM.mm_mode_to_flags" [CBV mode])) #;
          (#if (Call "MM.mm_ptable_identity_update" [CBV (load_at_i stage1_locked ptable_loc);
                                                    CBV a_begin; CBV a_end;
                                                    CBV (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode]);
                                                    CBV flags; CBR ppool])
            then Return (Call "ADDR.ptr_from_va" [CBV (Call "ADDR.va_from_pa" [CBV a_begin])])
            else Skip) #;
          Return Vnull.
  (*
  /**
   * Updates the hypervisor table such that the given physical address range is
   * not mapped in the address space.
   */
  bool mm_unmap(struct mm_stage1_locked stage1_locked, paddr_t begin, paddr_t end,
                struct mpool *ppool)
  {
          uint32_t mode = MM_MODE_UNMAPPED_MASK;
   
          return mm_identity_map(stage1_locked, begin, end, mode, ppool);
  }
  *)

  Definition mm_unmap (stage1_locked a_begin a_end ppool : var) (mode : var) :=
    mode #= MM_MODE_UNMAPPED_MASK #;
         Return (Call "MM.mm_identity_map" [CBR stage1_locked; CBV a_begin; CBV a_begin; CBR ppool]).
  

  (*
  /**
   * Defragments the hypervisor page table.
   */
  void mm_defrag(struct mm_stage1_locked stage1_locked, struct mpool *ppool)
  {
          mm_ptable_defrag(stage1_locked.ptable, MM_FLAG_STAGE1, ppool);
  }
  *)
   
  Definition mm_defrag (stage1_locked ppool : var) :=
    (Call "MM.mm_ptable_defrag" [CBV (load_at_i stage1_locked ptable_loc); CBV MM_FLAG_STAGE1; CBR ppool]).
  
  (*
  // JIEUNG: This one is about initialization, but we will ignore most of this
  // part
  /**
   * Initialises memory management for the hypervisor itself.
   */
  bool mm_init(struct mpool *ppool)
  {
          /* Locking is not enabled yet so fake it, */
          struct mm_stage1_locked stage1_locked = mm_stage1_lock_unsafe();
   
          dlog_info("text: %#x - %#x\n", pa_addr(layout_text_begin()),
          	  pa_addr(layout_text_end()));
          dlog_info("rodata: %#x - %#x\n", pa_addr(layout_rodata_begin()),
          	  pa_addr(layout_rodata_end()));
          dlog_info("data: %#x - %#x\n", pa_addr(layout_data_begin()),
          	  pa_addr(layout_data_end()));
   
          if (!mm_ptable_init(&ptable, MM_FLAG_STAGE1, ppool)) {
          	dlog_error("Unable to allocate memory for page table.\n");
          	return false;
          }
   
          /* Let console driver map pages for itself. */
          plat_console_mm_init(stage1_locked, ppool);
   
          /* Map each section. */
          mm_identity_map(stage1_locked, layout_text_begin(), layout_text_end(),
          		MM_MODE_X, ppool);
   
          mm_identity_map(stage1_locked, layout_rodata_begin(),
          		layout_rodata_end(), MM_MODE_R, ppool);
   
          mm_identity_map(stage1_locked, layout_data_begin(), layout_data_end(),
          		MM_MODE_R | MM_MODE_W, ppool);
   
          return arch_mm_init(ptable.root);
  }
  *)

  (* XXX: Do we need to contain LAYOUT functions in here? *)
  Definition mm_init (ppool : var) (stage1_locked : var) :=
    stage1_locked #= (Call "MM.mm_stage1_lock_unsafe" []) #;
                  (#if (#! (Call "MM.mm_ptable_init" [CBR ptable; CBV MM_FLAG_STAGE1; CBR ppool]))
                    then Return Vfalse
                    else Skip) #;
                  (* XXX: ignore the following line 
                          plat_console_mm_init(stage1_locked, ppool); *)
                  (Call "MM.mm_identity_map" [CBR stage1_locked;
                                             CBV (Call "LAYOUT.layout_text_begin" []);
                                             CBV (Call "LAYOUT.layout_text_end" []);
                                             CBV MM_MODE_X; CBR ppool]) #;                                             
                  (Call "MM.mm_identity_map" [CBR stage1_locked;
                                             CBV (Call "LAYOUT.layout_rodata_begin" []);
                                             CBV (Call "LAYOUT.layout_rodata_end" []);
                                             CBV MM_MODE_R; CBR ppool]) #;
                  (Call "MM.mm_identity_map" [CBR stage1_locked; 
                                             CBV (Call "LAYOUT.layout_data_begin" []);
                                             CBV (Call "LAYOUT.layout_data_end" []);
                                             CBV (MM_MODE_R #| MM_MODE_W); CBR ppool]) #;
                  Return (Call "ARCHMM.arch_mm_init" [CBV (load_at_i ptable root_loc)]).

  Definition mm_stage2_invalidate_falseF: function. mk_function_tac mm_stage2_invalidate_false ([]: list var) ([]: list var). Defined.
  Definition mm_vm_enable_invalidationF: function. mk_function_tac mm_stage2_invalidate_false ([]: list var) ([]: list var). Defined.
  Definition mm_page_table_from_paF: function. mk_function_tac mm_page_table_from_pa ["pa"] ([]:list var). Defined.
  Definition mm_round_down_to_pageF: function. mk_function_tac mm_round_down_to_page ["addr"] ([]:list var). Defined.
  Definition mm_round_up_to_pageF: function. mk_function_tac mm_round_up_to_page ["addr"] ([]:list var). Defined.
  Definition mm_entry_sizeF: function. mk_function_tac mm_entry_size ["level"] ([]:list var). Defined.
  Definition mm_start_of_next_blockF: function. mk_function_tac mm_start_of_next_block ["addr"; "block_size"] ([]:list var). Defined.
  Definition mm_pa_start_of_next_blockF: function. mk_function_tac mm_pa_start_of_next_block ["pa"; "block_size"] ([]:list var). Defined.
  Definition mm_level_endF: function. mk_function_tac mm_level_end ["addr"; "level"] (["offset"]:list var). Defined.
  Definition mm_indexF: function. mk_function_tac mm_index ["addr"; "level"] (["v"]:list var). Defined.
  Definition mm_alloc_page_tablesF: function. mk_function_tac mm_alloc_page_tables ["count"; "ppool"] ([]:list var). Defined.
  Definition mm_max_levelF: function. mk_function_tac mm_max_level ["flags"] ([]:list var). Defined.
  Definition mm_root_table_countF: function. mk_function_tac mm_root_table_count ["flags"] ([]:list var). Defined.
  Definition mm_invalidate_tlbF: function. mk_function_tac mm_invalidate_tlb ["a_begin"; "a_end"; "flags"] ([]:list var). Defined.
  Definition mm_free_page_pteF: function. mk_function_tac mm_free_page_pte ["pte"; "level"; "ppool"] ["table"; "i"]. Defined.
  Definition mm_ptable_addr_space_endF: function. mk_function_tac mm_ptable_addr_space_end ["flags"] ([]:list var). Defined.
  Definition mm_ptable_initF: function. mk_function_tac mm_ptable_init ["t"; "flags"; "ppool"] ["root_table_count"; "tables"; "i"; "j"]. Defined.
  Definition mm_ptable_finiF: function. mk_function_tac mm_ptable_fini ["t"; "flags"; "ppool"] ["tables"; "root_table_count"; "level"; "i"; "j"]. Defined.

  Definition mm_program: program :=
    [
      ("MM.mm_stage2_invalidate_false", mm_stage2_invalidate_falseF) ;
        ("MM.mm_vm_enable_invalidation", mm_vm_enable_invalidationF) ;
        ("MM.mm_page_table_from_pa", mm_page_table_from_paF) ;
        ("MM.mm_round_down_to_page", mm_round_down_to_pageF) ;
        ("MM.mm_round_up_to_page", mm_round_up_to_pageF) ;
        ("MM.mm_entry_size", mm_entry_sizeF) ;
        ("MM.mm_start_of_next_block", mm_start_of_next_blockF) ;
        ("MM.mm_pa_start_of_next_block", mm_pa_start_of_next_blockF) ;
        ("MM.mm_level_end", mm_level_endF) ;
        ("MM.mm_index", mm_indexF) ;
        ("MM.mm_alloc_page_tables", mm_alloc_page_tablesF) ;
        ("MM.mm_max_level", mm_max_levelF) ;
        ("MM.mm_root_table_count", mm_root_table_countF) ;
        ("MM.mm_invalidate_tlb", mm_invalidate_tlbF) ;        
        ("MM.mm_free_page_pte", mm_free_page_pteF) ;
        ("MM.mm_ptable_addr_space_end", mm_ptable_addr_space_endF) ;
        ("MM.mm_ptable_init", mm_ptable_initF) ;
        ("MM.mm_ptable_fini", mm_ptable_finiF)      
    ].
  
  Definition mm_modsem : ModSem := program_to_ModSem mm_program.

End MMCONCUR.
