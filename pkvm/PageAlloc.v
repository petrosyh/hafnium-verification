(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com)
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

(* begin hide *)

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

Require Import Decision.

Require Import Coqlib sflib.

Require Import Maps.
Set Implicit Arguments.

(*
#ifdef __SIZEOF_LONG__
#define BITS_PER_LONG (__CHAR_BIT__ * __SIZEOF_LONG__)
#else
#define BITS_PER_LONG __WORDSIZE
#endif
*)

(*
#define __GENMASK(h, l) \
	(((~UL(0)) - (UL(1) << (l)) + 1) & \
	 (~UL(0) >> (BITS_PER_LONG - 1 - (h))))
#define GENMASK(h, l) \
	(GENMASK_INPUT_CHECK(h, l) + __GENMASK(h, l))
 *)

(*  64 bits *)
Definition __CHAR_BIT__ := 8.
Definition __SIZEOF_LONG__ := 8.

Definition BITS_PER_LONG := __CHAR_BIT__ * __SIZEOF_LONG__.

Definition Z_LONG_MAX := ((Z.pow 2 BITS_PER_LONG) - 1)%Z.
Definition Z_LONG_NOT := fun val => (Z.lxor Z_LONG_MAX val).

(*
#ifdef CONFIG_PHYS_ADDR_T_64BIT
typedef u64 phys_addr_t;
#else
typedef u32 phys_addr_t;
#endif
 *)

Definition phys_addr_t := Z.

(* we may not need thie variable
#define MAX_PAGE_GROUPS 0x1000   /* horrible hack */

extern u64 __hyp_vmemmap;
#define hyp_vmemmap ((struct hyp_page * )__hyp_vmemmap)
 *)
Class MemProps :=
  {
  __hyp_vmemmap : Z;
  MAX_PAGE_GRUOPS : Z
  }.

Context `{mem_props : MemProps}.

Definition hyp_vmemmap := __hyp_vmemmap.

(*
#define PAGE_SHIFT      13
#ifdef __ASSEMBLY__
#define PAGE_SIZE       (1 << PAGE_SHIFT)
#else
#define PAGE_SIZE       (1UL << PAGE_SHIFT)
 *)

Definition PAGE_SHIFT := 13.
Definition PAGE_SIZE := Z.shiftl 1 PAGE_SHIFT.


(* 
#ifndef UINT_MAX
#define UINT_MAX	(~0U)
*)

Definition UNIT_MAX := Z_LONG_NOT 0.

(*

#define HYP_MAX_ORDER	11U
#define HYP_NO_ORDER	UINT_MAX
 *)

Definition HYP_MAX_ORDER := 11.
Definition HYP_NO_ORDER := UNIT_MAX.

(*
struct hyp_pool {
	hyp_spinlock_t lock;
	struct list_head free_area[HYP_MAX_ORDER + 1];
	phys_addr_t range_start;
	phys_addr_t range_end;
};
 *)

Record hyp_pool :=
  mkhyp_pool {
      free_area : list Z; (* index lists of hyp_pool *)
      range_start : phys_addr_t;
      range_end : phys_addr_t;
      used_pages : Z; (* number of pages that are used *)
    }.

Definition hyp_pools := ZTree.t hyp_pool.
      
(*
/* GFP flags */
#define HYP_GFP_NONE	0
#define HYP_GFP_ZERO	1

 *)

Definition HYP_GFP_NONE := 0.
Definition HYP_GFP_ZERO := 1.

(*
struct hyp_page {
	unsigned int refcount;
	unsigned int order;
	struct hyp_pool *pool;
	struct list_head node;
};
*)

Record hyp_page :=
  mkhyp_page {
      refcount : Z;
      order_in_hyp_page : Z;
      pool : Z (* id of hyp_pools *)
    }.               
                   

(*
struct page_group {
	phys_addr_t start;
	unsigned int order;
	bool free;
};
1 *)

Record page_group :=
  mkpage_group {
      start :phys_addr_t;
      order : Z;
      free : bool
    }.

(* 
#define hyp_page_to_phys(page)  ((phys_addr_t)((page) - hyp_vmemmap) << PAGE_SHIFT)
 *)

Class MemAuxiliaryFunctions :=
  {
  hyp_page_to_phys : Z -> phys_addr_t;
  }.

Instance mem_auxiliary_functions : MemAuxiliaryFunctions :=
  {
  hyp_page_to_phys :=
    fun page => Z.shiftl (page - hyp_vmemmap) PAGE_SHIFT
  }.

(*
struct page_groups {
	struct page_group page_group[MAX_PAGE_GROUPS];
	u64 count;
};
 *)

Definition page_groups := ZTree.t page_group.

(*  
struct page_groups page_groups_a;
*)

(*
bool in_used_pages(phys_addr_t phys, struct hyp_pool *pool)
{
	return phys < pool->range_start + PAGE_SIZE*pool->used_pages;
}
 *)

Definition in_used_pages (phys : phys_addr_t) (pool: hyp_pool) :=
  decide (phys < pool.(range_start) + PAGE_SIZE * (pool.(used_pages))).

(* 
bool check_free_list(struct list_head *head, unsigned int order, struct hyp_pool *pool)
{
	bool ret;
	struct list_head *pos;
	struct hyp_page *p;
	phys_addr_t phys;
	ret = true;
	list_for_each(pos, head) { //for (pos = head->next; pos != (head); pos = pos->next) {
		p = list_entry(pos, struct hyp_page, node);
		phys = hyp_page_to_phys(p);
		if (phys < pool->range_start + PAGE_SIZE*pool->used_pages || phys >= pool->range_end) { ret=false; hyp_putsxn("phys",(u64)phys,64); check_assert_fail("free list entry not in pool unused_page range"); } // maybe this should check p is the address of a hyp_page node member, not just go straight to hyp_page_to_phys's notion of phys 
		if (p->order != order) { ret=false; hyp_putsxn("phys",(u64)phys,64); check_assert_fail("free list entry has wrong order"); }
	}
	return ret;
}
 *)



(*
/* well-formed free lists of pool */
bool check_free_lists(struct hyp_pool *pool)
{
	u64 i;
	bool ret;
	ret = true;
	for (i=0; i<HYP_MAX_ORDER+1; i++) {
		ret = ret && check_free_list(&pool->free_area[i], i, pool);
	}
	return ret;
}
*)



