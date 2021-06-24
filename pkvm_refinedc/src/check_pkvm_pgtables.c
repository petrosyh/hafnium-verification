#include <assert.h> 

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


/*
 * BUILD_BUG_ON_ZERO is not available in h files included from asm files,
 * disable the input check if that is the case.
 */

#define BITS_PER_LONG 64 

#define __GENMASK(h, l) \
        (((~0) - (1 << (l)) + 1) & \
         (~0 >> (BITS_PER_LONG - 1 - (h))))
#define GENMASK(h, l) (__GENMASK(h, l))

// the logical entry kinds
enum entry_kind {
  EK_INVALID,
  EK_BLOCK,
  EK_TABLE,
  EK_PAGE_DESCRIPTOR,
  EK_BLOCK_NOT_PERMITTED,
  EK_RESERVED,
  EK_DUMMY
};

// the entry kind bit representations
#define ENTRY_INVALID_0 0
#define ENTRY_INVALID_2 2
#define ENTRY_BLOCK 1
#define ENTRY_RESERVED 1
#define ENTRY_PAGE_DESCRIPTOR 3
#define ENTRY_TABLE 3

// compute the entry_kind of a page-table entry
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

struct FaultRecord {
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

struct FullAddress {
        unsigned long long address; // bits(52) address;
        int NS;          // bit NS; // '0' = Secure, '1' = Non-secure
};

struct AddressDescriptor {
        struct FaultRecord fault; // fault.statuscode indicates whether the address is valid
        //  MemoryAttributes memattrs;
        struct FullAddress paddress;
        unsigned long long vaddress; // bits(64) vaddress;
};

//struct Permissions {
// bits(3) ap; // Access permission bits
// bit xn; // Execute-never bit
// bit xxn; // [Armv8.2] Extended execute-never bit for stage 2
// bit pxn // Privileged execute-never bit
//}


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
