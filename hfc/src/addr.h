/*
 * Copyright 2018 The Hafnium Authors.
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
 */

#pragma once

#include <stddef.h>
#include <stdint.h>

#include "hf/arch/types.h"


// JIEUNG

/** The type of a page table entry (PTE). */
// typedef uint64_t pte_t;

/** Integer type large enough to hold a physical address. */
// typedef uintptr_t uintpaddr_t;

/** Integer type large enough to hold a virtual address. */
// typedef uintptr_t uintvaddr_t;

/** The integer type corresponding to the native register size. */
// typedef uint64_t uintreg_t;

/** The ID of a physical or virtual CPU. */
// typedef uint64_t cpu_id_t;

/** A bitset for AArch64 CPU features. */
// typedef uint64_t arch_features_t;




/** An opaque type for a physical address. */
typedef struct {
	uintpaddr_t pa;
} paddr_t;

/** An opaque type for an intermediate physical address. */
typedef struct {
	uintpaddr_t ipa;
} ipaddr_t;

/** An opaque type for a virtual address. */
typedef struct {
	uintvaddr_t va;
} vaddr_t;

/**
 * Initializes a physical address.
 */
static inline paddr_t pa_init(uintpaddr_t p)
{
	return (paddr_t){.pa = p};
}

/**
 * Extracts the absolute physical address.
 */
static inline uintpaddr_t pa_addr(paddr_t pa)
{
	return pa.pa;
}

/**
 * Advances a physical address.
 */
static inline paddr_t pa_add(paddr_t pa, size_t n)
{
	return pa_init(pa_addr(pa) + n);
}

/**
 * Returns the difference between two physical addresses.
 */
static inline size_t pa_difference(paddr_t start, paddr_t end)
{
	return pa_addr(end) - pa_addr(start);
}

/**
 * Initializes an intermeditate physical address.
 */
static inline ipaddr_t ipa_init(uintpaddr_t ipa)
{
	return (ipaddr_t){.ipa = ipa};
}

/**
 * Extracts the absolute intermediate physical address.
 */
static inline uintpaddr_t ipa_addr(ipaddr_t ipa)
{
	return ipa.ipa;
}

/**
 * Advances an intermediate physical address.
 */
static inline ipaddr_t ipa_add(ipaddr_t ipa, size_t n)
{
	return ipa_init(ipa_addr(ipa) + n);
}

/**
 * Initializes a virtual address.
 */
static inline vaddr_t va_init(uintvaddr_t v)
{
	return (vaddr_t){.va = v};
}

/**
 * Extracts the absolute virtual address.
 */
static inline uintvaddr_t va_addr(vaddr_t va)
{
	return va.va;
}

/**
 * Casts a physical address to a virtual address.
 */
static inline vaddr_t va_from_pa(paddr_t pa)
{
	return va_init(pa_addr(pa));
}



// JIEUNG: it is just casting. So, we do not translate the addresss itself 
/**
 * Casts a physical address to an intermediate physical address.
 */
static inline ipaddr_t ipa_from_pa(paddr_t pa)
{
	return ipa_init(pa_addr(pa));
}

/**
 * Casts a virtual address to a physical address.
 */
static inline paddr_t pa_from_va(vaddr_t va)
{
	return pa_init(va_addr(va));
}

/**
 * Casts an intermediate physical address to a physical address.
 */
static inline paddr_t pa_from_ipa(ipaddr_t ipa)
{
	return pa_init(ipa_addr(ipa));
}

/**
 * Casts a pointer to a virtual address.
 */
static inline vaddr_t va_from_ptr(const void *p)
{
	return (vaddr_t){.va = (uintvaddr_t)p};
}



// JIEUNG: Do we actually need this one? we always call this one via
// (ptr_from_va(va_from_pa(...))) ...
/**
 * Casts a virtual address to a pointer. Only use when the virtual address is
 * mapped for the calling context.
 * TODO: check the mapping for a range and return a memiter?
 */
static inline void *ptr_from_va(vaddr_t va)
{
	return (void *)va_addr(va);
}
