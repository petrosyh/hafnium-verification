#include <assert.h> 

//@rc::import page_table_entry_type from refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables
//@rc::import Decision from refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables

// The following defines aliasings for type names.
// They are defined in two files in the repository
// 1. include/uapi/asm-generic/int-l64.h
// 2. include/uapi/asm-generic/int-ll64.h

// Among them, I couldn't find out the proper file for this implementation. 
// So, I am currently working on this file based on
// "include/uapi/asm-generic/int-l64.h"
// [XXX(JK) - We may need to find out the proper file among those two]

/*
 * __xx is ok: it doesn't pollute the POSIX namespace. Use these in the
 * header files exported to user space
 */

// In the below, __signed__ is the keyword that may be generated via lex and
// yacc. 
// The relevant files are scripts/genksyms/keywords.c, scripts/genksyms/lex.l,
// and scripts/genksyms/parse.y.
// [XXX(JK) - Do we need to think about what we can do with those things?]
/*
typedef __signed__ char __s8;
typedef unsigned char __u8;

typedef __signed__ short __s16;
typedef unsigned short __u16;

typedef __signed__ int __s32;
typedef unsigned int __u32;

typedef __signed__ long __s64;
typedef unsigned long __u64;
*/

typedef signed char __s8;
typedef unsigned char __u8;

typedef signed short __s16;
typedef unsigned short __u16;

typedef signed int __s32;
typedef unsigned int __u32;

typedef signed long __s64;
typedef unsigned long __u64;


// #ifndef __ASSEMBLY__
// /*
//  * __xx is ok: it doesn't pollute the POSIX namespace. Use these in the
//  * header files exported to user space
//  */
//
// typedef __signed__ char __s8;
// typedef unsigned char __u8;
//
// typedef __signed__ short __s16;
// typedef unsigned short __u16;
//
// typedef __signed__ int __s32;
// typedef unsigned int __u32;
//
// #ifdef __GNUC__
// __extension__ typedef __signed__ long long __s64;
// __extension__ typedef unsigned long long __u64;
// #else
// typedef __signed__ long long __s64;
// typedef unsigned long long __u64;
// #endif
//
// #endif /* __ASSEMBLY__ */

// There are three files that contain GENMASK definitions 
// 1. include/linux/bits.h
// 2. tools/include/linux/bits.h
// 3. tools/power/x86/intel-speed-select/isst.h
//
// Among them, include/linux/bits.h is used in this file. 

// GENMASK is one of the most important definition here. The top level GENMASK
// definition relies on several definitions, but the top most one is in 
/*
 * BUILD_BUG_ON_ZERO is not available in h files included from asm files,
 * disable the input check if that is the case.
 */

// In include/uapi/linux/const.h, It defines UL, ULL based on several
// definitions. We define them.


// XXX(JK) - The following definition raises errors (may be... due to X##Y. 
// Therefore, I changed it...
// RefinedC has to be extended to cover them
#define __AC(X,Y)       (X##Y)
#define _AC(X,Y)        __AC(X,Y)

#define _UL(x)          (_AC(x, UL))

// In include/vdso/const.h (It is imported into "include/linux/bits.h" via 
// include/linux/const.h
/* XXX(JK) - It is also changed due to the error
#define UL(x)           (_UL(x))
*/

// In include/asm-generic/bitsperlong.h, it defines BITS_PER_LONG and other
// related definitions. The file also imports include/uapi/asm-generic/bitsperlong.h
// [XXX(JK) - It depends on CONFIG_64BIT, but I ignore the definition]

#define BITS_PER_LONG 64
#define BITS_PER_LONG_LONG 64

// include/linux/build_bug.h
// GENMASK_INPUT_CHECK uses BUILD_BUG_ON_ZERO. 
// This BUILD_BUG_ON_ZERO is defined in multiple places. 
// 1. include/linux/build_bug.h
// 2. tools/include/linux/bug.h
// 3. tools/include/linux/build_bug.h

// Among them, "include/linux/bits.h" explicitly imports
// "include/linux/build_bug.h" in it.

#define BUILD_BUG_ON_ZERO(e) ((int)(sizeof(struct { int:(-!!(e)); })))

// include/linux/bits.h

// The following GENMASK_INPUT_CHECK relies on two builtin functions in 
// GNU GCC. 
//
// They are __builtin_choose_expr and __builtin_constant_p
// Please look at https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html for
// the full explanation about it 
//
// Built-in Function: type __builtin_choose_expr (const_exp, exp1, exp2)
// You can use the built-in function __builtin_choose_expr to evaluate code depending on the value of a constant expression. This built-in function returns exp1 if const_exp, which is an integer constant expression, is nonzero. Otherwise it returns exp2.

// This built-in function is analogous to the ‘? :’ operator in C, except that the expression returned has its type unaltered by promotion rules. Also, the built-in function does not evaluate the expression that is not chosen. For example, if const_exp evaluates to true, exp2 is not evaluated even if it has side effects.

// This built-in function can return an lvalue if the chosen argument is an lvalue.

// If exp1 is returned, the return type is the same as exp1’s type. Similarly, if exp2 is returned, its return type is the same as exp2.

// Built-in Function: int __builtin_constant_p (exp)
// You can use the built-in function __builtin_constant_p to determine if a value is known to be constant at compile time and hence that GCC can perform constant-folding on expressions involving that value. The argument of the function is the value to test. The function returns the integer 1 if the argument is known to be a compile-time constant and 0 if it is not known to be a compile-time constant. A return of 0 does not indicate that the value is not a constant, but merely that GCC cannot prove it is a constant with the specified value of the -O option.


// [XXX(JK) - The original definition raises errors. I changed the definition.]
#define __builtin_choose_expr(const_exp, exp1, exp2) (const_exp ? exp1 : exp2)
#define __builtin_constant_p(exp) (exp)
/*
#define GENMASK_INPUT_CHECK(h, l) \
        (BUILD_BUG_ON_ZERO(__builtin_choose_expr( \
                __builtin_constant_p((l) > (h)), (l) > (h), 0)))

#define __GENMASK(h, l) \
        (((~UL(0)) - (UL(1) << (l)) + 1) & \
         (~UL(0) >> (BITS_PER_LONG - 1 - (h))))

#define GENMASK(h, l) \
        (GENMASK_INPUT_CHECK(h, l) + __GENMASK(h, l))
*/

#define __GENMASK(h, l) \
        (((~0UL) - (1UL << (l)) + 1) & \
         (~0UL >> (BITS_PER_LONG - 1 - (h))))
#define GENMASK(h, l) \
        __GENMASK(h, l)

// the logical entry kinds
typedef enum entry_kind {
  EK_INVALID,
  EK_BLOCK,
  EK_TABLE,
  EK_PAGE_DESCRIPTOR,
  EK_BLOCK_NOT_PERMITTED,
  EK_RESERVED,
  EK_DUMMY
} entry_kind_type;

// the entry kind bit representations
#define ENTRY_INVALID_0 0
#define ENTRY_INVALID_2 2
#define ENTRY_BLOCK 1
#define ENTRY_RESERVED 1
#define ENTRY_PAGE_DESCRIPTOR 3
#define ENTRY_TABLE 3


[[rc::parameters("zpte: Z", "zlevel : Z")]]
[[rc::args("zpte @ int<u64>", "zlevel @ int<u8>")]]
// [[rc::requires("{ 0 ≤ (GENMASK_0_1 zpte)}")]]
// [[rc::returns("ENTRY_TYPE")]]
// [[rc::returns("int<u32>")]]
// compute the entry_kind of a page-table entry
[[rc::requires("{well_formed_page_table_entry zpte zlevel}")]]
[[rc::exists("res : Z")]]
[[rc::returns("res @ int<u32>")]]
// [[rc::exists("pte_val : {PTE_TYPES}")]]
// [[rc::exists("entry_type: {ENTRY_TYPE}")]]
// [[rc::ensures("{Z_to_PTE_TYPES zpte zlevel = Some pte_val}")]]
//[[rc::ensures("{GET_PTE_TYPES pte_val = entry_type}")]]
//[[rc::ensures("{PTE_TYPE_VALUE_EQUIV entry_type res}")]]
enum entry_kind entry_kind(unsigned long long pte, unsigned char level)
{
        switch(level) {
        case 0:
        case 1:
        case 2:
        {
                switch (pte & GENMASK(1,0)) {
                case ENTRY_INVALID_0:
                case ENTRY_INVALID_2:
                        return EK_INVALID;
                case ENTRY_BLOCK:
                        switch (level)
                        {
                        case 0:
                                return EK_BLOCK_NOT_PERMITTED;
                        case 1:
                        case 2:
                                return EK_BLOCK;
                        }
                case ENTRY_TABLE:
                        return EK_TABLE;
                default:
                        return EK_DUMMY; // just to tell the compiler that the cases are exhaustive
                }
        }
        case 3:
                switch (pte & GENMASK(1,0)) {
                case ENTRY_INVALID_0:
                case ENTRY_INVALID_2:
                        return EK_INVALID;
                case ENTRY_RESERVED:
                        return EK_RESERVED;
                case ENTRY_PAGE_DESCRIPTOR:
                        return EK_PAGE_DESCRIPTOR;
                }

        default:
                return EK_DUMMY; // just to tell the compiler that the cases are exhaustive
        }

        return EK_DUMMY;
}


enum Fault {
        Fault_None,
        Fault_AccessFlag,
        Fault_Alignment,
        Fault_Background,
        Fault_Domain,
        Fault_Permission,
        Fault_Translation,
        Fault_AddressSize,
        Fault_SyncExternal,
        Fault_SyncExternalOnWalk,
        Fault_SyncParity,
        Fault_SyncParityOnWalk,
        Fault_AsyncParity,
        Fault_AsyncExternal,
        Fault_Debug,
        Fault_TLBConflict,
        Fault_BranchTarget,
        Fault_HWUpdateAccessFlag,
        Fault_Lockdown,
        Fault_Exclusive,
        Fault_ICacheMaint
};

struct
[[rc::refined_by("statuscode : Z")]]
[[rc::ptr_type("fault_record : ...")]]
FaultRecord {
  [[rc::field("statuscode @ int<u32>")]]
  enum Fault statuscode; // Fault Status
  //  AccType acctype; // Type of access that faulted
  //  FullAddress ipaddress; // Intermediate physical address
  //  boolean s2fs1walk; // Is on a Stage 1 page table walk
  //  boolean write; // TRUE for a write, FALSE for a read
  //  integer level; // For translation, access flag and permission faults
  //  bit extflag; // IMPLEMENTATION DEFINED syndrome for external aborts
  //  boolean secondstage; // Is a Stage 2 abort
  //  bits(4) domain; // Domain number, AArch32 only
  //  bits(2) errortype; // [Armv8.2 RAS] AArch32 AET or AArch64 SET
  //  bits(4) debugmoe; // Debug method of entry, from AArch32 only
};

struct 
[[rc::refined_by("address : Z", "NS : Z")]]
[[rc::ptr_type("full_address : ...")]]
FullAddress {
  [[rc::field("address @ int<u64>")]]
  unsigned long long address; // bits(52) address;
  // Can we annotate it with 1
  [[rc::field("NS @ int<u32>")]]
  int NS; // bit NS; // '0' = Secure, '1' = Non-secure
};

struct 
// [[rc::refined_by("fault : fault_record", "paddr : full_address", "vaddress: Z")]]
// [[rc::ptr_type("address_descriptor : ... ")]]
AddressDescriptor {
  // [[rc::field("fault @ fault_record")]]
  struct FaultRecord fault; // fault.statuscode indicates whether the address is valid
  //  MemoryAttributes memattrs;
  // [[rc::field("paddress @ full_address")]]
  struct FullAddress paddress;
  // [[rc::field("vaddress @ int<u64>")]]
  unsigned long long vaddress; // bits(64) vaddress;
};

//struct Permissions {
// bits(3) ap; // Access permission bits
// bit xn; // Execute-never bit
// bit xxn; // [Armv8.2] Extended execute-never bit for stage 2
// bit pxn // Privileged execute-never bit
//}

struct TLBRecord {
 	//  Permissions        perms;
	//  bit 	             nG;	   // '0' = Global, '1' = not Global
	//  bits(4)	     domain;	   // AArch32 only
	//  bit		     GP;	   // Guarded Page
	//  boolean	     contiguous;   // Contiguous bit from page table
	//  integer	     level;	   // AArch32 Short-descriptor format: Indicates Section/Page
	//  integer	     blocksize;    // Describes size of memory translated in KBytes
	//  DescriptorUpdate   descupdate;   // [Armv8.1] Context for h/w update of table descriptor
	//  bit		     CnP;	   // [Armv8.2] TLB entry can be shared between different PEs
	struct AddressDescriptor  addrdesc;
};


// [[rc::parameters("vvaddress: Z")]]
// [[rc::args("vvaddress @ int<u64>")]]
struct TLBRecord mkFault(unsigned long long vaddress) {
  struct TLBRecord result;
  result.addrdesc.fault.statuscode = Fault_Translation;
  result.addrdesc.paddress.address = 0;
  result.addrdesc.paddress.NS = 0;
  result.addrdesc.vaddress = vaddress;

  return result;
}

/*
struct TLBRecord mkFault_error(unsigned long long vaddress) {
	struct TLBRecord r = { .addrdesc = { .fault = { .statuscode=Fault_Translation } , .paddress =  { .address=0, .NS=0 }, .vaddress = vaddress } };
	return r;
	// massively oversimplified
} */


// aarch64/translation/walk/AArch64.TranslationTableWalk
// TLBRecord AArch64.TranslationTableWalk(bits(52) ipaddress, boolean s1_nonsecure, bits(64) vaddress, AccType acctype, boolean iswrite, boolean secondstage, boolean s2fs1walk, integer size)

// There's a lot of detailed code here, but most relates to options
// that I think are irrelevant for us. The actual walk is the repeat
// loop on p7729-7730.  For now, I'll try for something clean that
// handles only the basic VA->PA part, ignoring attributes etc., not
// to follow the ASL closely.

// I've done this recursively, but we might well want to unfold
// explicitly, eg to more easily check the correspondence between
// the ASL and the compiled implementation of this

/*  */
// note that we have some initializations for this variable in 
// arch/arm64/kvm/va_layout.c
signed long long hyp_physvirt_offset;
typedef signed long long phys_addr_t;

#define CHOOSE_NVHE_SYM(sym) sym
#define hyp_physvirt_offset CHOOSE_NVHE_SYM(hyp_physvirt_offset)

#define __hyp_va(phys)  ((void *)((phys_addr_t)(phys) - hyp_physvirt_offset))

static inline void *hyp_phys_to_virt(phys_addr_t phys)
{
        return __hyp_va(phys);
}

signed long long 
AArch64_TranslationTableWalk(unsigned long long table_base, 
                             unsigned long long level,
                             unsigned long long vaddress) {
        // these declarations should really be combined with their
        // initialisations below, but the compiler complains that ISO C90
        // forbids mixed declations and code
        unsigned long long pte;
        unsigned long long table_base_next_virt, table_base_next_phys;

        unsigned long long offset = 0; // offset in bytes of entry from table_base
        switch (level) {
        case 0: offset = (vaddress & GENMASK(47,39)) >> (39-3); break;
        case 1: offset = (vaddress & GENMASK(38,30)) >> (30-3); break;
        case 2: offset = (vaddress & GENMASK(29,21)) >> (21-3); break;
        case 3: offset = (vaddress & GENMASK(20,12)) >> (12-3); break;
        default: return (-1 * vaddress); // this is just to tell the compiler that the cases are exhaustive
        }

        // the actual page table entry
        pte = *((unsigned long long*)(table_base + offset));

        switch(level) {
        case 3:
                switch (pte & GENMASK(1,0)) {
                case ENTRY_INVALID_0:
                case ENTRY_INVALID_2:
                case ENTRY_BLOCK:
                        // invalid or fault entry
                        return (-1 * vaddress);
                case ENTRY_PAGE_DESCRIPTOR: // page descriptor
                        return ((pte & GENMASK(47,12)) | (vaddress & GENMASK(11,0)));
                }

        case 0:
        case 1:

        case 2:
        {
                switch (pte & GENMASK(1,0)) {
                case ENTRY_INVALID_0:
                case ENTRY_INVALID_2:
                        return (-1 * vaddress);
                case ENTRY_BLOCK:
                        switch (level) {
                        case 0:
                                return (-1 * vaddress);
                        case 1:
                                return ((pte & GENMASK(47,30)) | (vaddress & GENMASK(29,0)));
                        case 2:
                                return ((pte & GENMASK(47,21)) | (vaddress & GENMASK(20,0)));
                        }
                case ENTRY_TABLE: // recurse
                {
                        table_base_next_phys = pte & GENMASK(47,12);
                        table_base_next_virt = 
                            (unsigned long long)hyp_phys_to_virt
                            ((phys_addr_t)table_base_next_phys);

                        return AArch64_TranslationTableWalk(table_base_next_virt, level+1, vaddress);
                }
                default: return (-1 * vaddress); // this is just to tell the compiler that the cases are exhaustive
                }
        }
        default: return (-1 * vaddress); // this is just to tell the compiler that the cases are exhaustive
        }
}


int main() {
  unsigned long long pte;
  unsigned char level;

  pte = 10; 
  level = 3;

  enum entry_kind ek = entry_kind(pte, level);

  // printf("entry_kind %d\n", entry_kind);

  return 0;
}
