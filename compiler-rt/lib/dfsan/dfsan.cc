//===-- dfsan.cc ----------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is a part of DataFlowSanitizer.
//
// DataFlowSanitizer runtime.  This file defines the public interface to
// DataFlowSanitizer as well as the definition of certain runtime functions
// called automatically by the compiler (specifically the instrumentation pass
// in llvm/lib/Transforms/Instrumentation/DataFlowSanitizer.cpp).
//
// The public interface is defined in include/sanitizer/dfsan_interface.h whose
// functions are prefixed dfsan_ while the compiler interface functions are
// prefixed __dfsan_.
//===----------------------------------------------------------------------===//

#include "sanitizer_common/sanitizer_atomic.h"
#include "sanitizer_common/sanitizer_common.h"
#include "sanitizer_common/sanitizer_file.h"
#include "sanitizer_common/sanitizer_flags.h"
#include "sanitizer_common/sanitizer_flag_parser.h"
#include "sanitizer_common/sanitizer_libc.h"

#include "dfsan/dfsan.h"

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <string.h>

using namespace __dfsan;

typedef atomic_uint32_t atomic_dfsan_label;

// In Discovery mode, we create a new label for each LLVM IR instruction
// execution. This means the original limit of 2^16 labels is insufficient.
// 2^32 is too much static memory allocation, so we settle on a compromise.
// Dynamic Data-Flow graphs of more than 1000000 nodes are unlikely to be
// useful.
// FIXME: update shadow memory areas for other platforms than Linux/x86_64.
// FIXME: update union table memory areas (in Discovery mode, these are unused).
static const uptr kNumLabels = 1000000;

static const dfsan_label kInitializingLabel = kNumLabels - 1;

static atomic_dfsan_label __dfsan_last_label;
static atomic_dfsan_label __dfsan_last_execution;
static dfsan_label_info __dfsan_label_info[kNumLabels];

Flags __dfsan::flags_data;

SANITIZER_INTERFACE_ATTRIBUTE THREADLOCAL dfsan_label __dfsan_retval_tls;
SANITIZER_INTERFACE_ATTRIBUTE THREADLOCAL dfsan_label __dfsan_arg_tls[64];

SANITIZER_INTERFACE_ATTRIBUTE uptr __dfsan_shadow_ptr_mask;

typedef atomic_uint32_t atomic_dfsan_id;
static atomic_dfsan_id __dfsan_last_id{0};
static FILE *__dfsan_trace = NULL;

// Linux thread ID of the initial thread.
static pid_t base_tid{0};

typedef unsigned int dfsan_id;
// Maximum number of threads to trace.

// NOTE: this models assumes Linux assigns consecutive IDs to new threads, which
// requires tracing the program in isolation. The model could be generalized to
// arbitrary IDs by using dictionaries, e.g.
// https://stackoverflow.com/a/4384446 from K&R.
static const uptr kNumThreads = 32;
// Tracing mode (instruction or region-level) within each thread.
static bool __dfsan_instruction_tracing[kNumThreads];
// Current region ID within each thread.
static dfsan_id __dfsan_region_id[kNumThreads];
// Current region label within each thread.
static dfsan_label __dfsan_region_label[kNumThreads];

// Tag counters are used to count tag groups and instances.
typedef unsigned int tag_counter;
typedef atomic_uint32_t atomic_tag_counter;

// Last tag instance (this is global, as the specific instance assigned does not
// matter, only that they differ among instances).
static atomic_tag_counter __dfsan_last_tag_instance{0};

struct tag {
  const char *key;
  tag_counter group;
  tag_counter instance;
  struct tag *next;
};


void insert_tag(struct tag **head, const char *_key, tag_counter _group,
                tag_counter _instance) {
  struct tag *node = (struct tag *) malloc(sizeof(struct tag));
  assert(node);
  node->key = _key;
  node->group = _group;
  node->instance = _instance;
  node->next = *head;
  *head = node;
}

void remove_tag(struct tag **head, const char *_key) {
  struct tag* tmp = *head, *prev;
  if (tmp != NULL && strcmp(tmp->key, _key) == 0) {
    *head = tmp->next;
    free(tmp);
    return;
  }
  while (tmp != NULL && strcmp(tmp->key, _key) != 0) {
    prev = tmp;
    tmp = tmp->next;
  }
  if (tmp == NULL) {
    Report("NOTE: DataFlowSanitizer: ignoring removal of nonexistent tag %s\n",
           _key);
    return;
  }
  prev->next = tmp->next;
  free(tmp);
}

struct tag *find_tag(struct tag **head, const char *_key) {
  struct tag* tmp = *head, *prev;
  if (tmp != NULL && strcmp(tmp->key, _key) == 0) {
    return tmp;
  }
  while (tmp != NULL && strcmp(tmp->key, _key) != 0) {
    prev = tmp;
    tmp = tmp->next;
  }
  return tmp;
}

bool exists_tag(struct tag **head, const char *_key) {
  return find_tag(head, _key) != NULL;
}

void increment_tag_group(struct tag **head, const char *_key) {
  struct tag* t = find_tag(head, _key);
  if (t == NULL) {
    // The tag instance (last element) is irrelevant and set arbitrarily to 0.
    insert_tag(head, _key, 1, 0);
  } else {
    t->group++;
  }
}

// Active tags (linked list) within each thread.
static struct tag* __dfsan_tags[kNumThreads];

// Current group of each seen tag (linked list) within each thread. The tag
// instance field of each tag struct is ignored.
static struct tag* __dfsan_tag_groups[kNumThreads];

// On Linux/x86_64, memory is laid out as follows:
//
// +--------------------+ 0x800000000000 (top of memory)
// | application memory |
// +--------------------+ 0x700000008000 (kAppAddr)
// |                    |
// |       unused       |
// |                    |
// +--------------------+ 0x200200000000 (kUnusedAddr)
// |    union table     |
// +--------------------+ 0x200000000000 (kUnionTableAddr)
// |   shadow memory    |
// +--------------------+ 0x000000010000 (kShadowAddr)
// | reserved by kernel |
// +--------------------+ 0x000000000000
//
// To derive a shadow memory address from an application memory address,
// bits 44-46 are cleared to bring the address into the range
// [0x000000008000,0x100000000000).  Then the address is shifted left by 1 to
// account for the double byte representation of shadow labels and move the
// address into the shadow memory range.  See the function shadow_for below.

// On Linux/MIPS64, memory is laid out as follows:
//
// +--------------------+ 0x10000000000 (top of memory)
// | application memory |
// +--------------------+ 0xF000008000 (kAppAddr)
// |                    |
// |       unused       |
// |                    |
// +--------------------+ 0x2200000000 (kUnusedAddr)
// |    union table     |
// +--------------------+ 0x4000000000 (kUnionTableAddr)
// |   shadow memory    |
// +--------------------+ 0x0000010000 (kShadowAddr)
// | reserved by kernel |
// +--------------------+ 0x0000000000

// On Linux/AArch64 (39-bit VMA), memory is laid out as follow:
//
// +--------------------+ 0x8000000000 (top of memory)
// | application memory |
// +--------------------+ 0x7000008000 (kAppAddr)
// |                    |
// |       unused       |
// |                    |
// +--------------------+ 0x1200000000 (kUnusedAddr)
// |    union table     |
// +--------------------+ 0x1000000000 (kUnionTableAddr)
// |   shadow memory    |
// +--------------------+ 0x0000010000 (kShadowAddr)
// | reserved by kernel |
// +--------------------+ 0x0000000000

// On Linux/AArch64 (42-bit VMA), memory is laid out as follow:
//
// +--------------------+ 0x40000000000 (top of memory)
// | application memory |
// +--------------------+ 0x3ff00008000 (kAppAddr)
// |                    |
// |       unused       |
// |                    |
// +--------------------+ 0x1200000000 (kUnusedAddr)
// |    union table     |
// +--------------------+ 0x8000000000 (kUnionTableAddr)
// |   shadow memory    |
// +--------------------+ 0x0000010000 (kShadowAddr)
// | reserved by kernel |
// +--------------------+ 0x0000000000

// On Linux/AArch64 (48-bit VMA), memory is laid out as follow:
//
// +--------------------+ 0x1000000000000 (top of memory)
// | application memory |
// +--------------------+ 0xffff00008000 (kAppAddr)
// |       unused       |
// +--------------------+ 0xaaaab0000000 (top of PIE address)
// | application PIE    |
// +--------------------+ 0xaaaaa0000000 (top of PIE address)
// |                    |
// |       unused       |
// |                    |
// +--------------------+ 0x1200000000 (kUnusedAddr)
// |    union table     |
// +--------------------+ 0x8000000000 (kUnionTableAddr)
// |   shadow memory    |
// +--------------------+ 0x0000010000 (kShadowAddr)
// | reserved by kernel |
// +--------------------+ 0x0000000000

typedef atomic_dfsan_label dfsan_union_table_t[kNumLabels][kNumLabels];

#ifdef DFSAN_RUNTIME_VMA
// Runtime detected VMA size.
int __dfsan::vmaSize;
#endif

static uptr UnusedAddr() {
  return MappingArchImpl<MAPPING_UNION_TABLE_ADDR>()
         + sizeof(dfsan_union_table_t);
}

static atomic_dfsan_label *union_table(dfsan_label l1, dfsan_label l2) {
  return &(*(dfsan_union_table_t *) UnionTableAddr())[l1][l2];
}

// Checks we do not run out of labels.
static void dfsan_check_label(dfsan_label label) {
  if (label == kInitializingLabel) {
    Report("FATAL: DataFlowSanitizer: out of labels\n");
    Die();
  }
}

// Resolves the union of two unequal labels.  Nonequality is a precondition for
// this function (the instrumentation pass inlines the equality test).
extern "C" SANITIZER_INTERFACE_ATTRIBUTE
dfsan_label __dfsan_union(dfsan_label l1, dfsan_label l2) {
  DCHECK_NE(l1, l2);

  if (l1 == 0)
    return l2;
  if (l2 == 0)
    return l1;

  if (l1 > l2)
    Swap(l1, l2);

  atomic_dfsan_label *table_ent = union_table(l1, l2);
  // We need to deal with the case where two threads concurrently request
  // a union of the same pair of labels.  If the table entry is uninitialized,
  // (i.e. 0) use a compare-exchange to set the entry to kInitializingLabel
  // (i.e. -1) to mark that we are initializing it.
  dfsan_label label = 0;
  if (atomic_compare_exchange_strong(table_ent, &label, kInitializingLabel,
                                     memory_order_acquire)) {
    // Check whether l2 subsumes l1.  We don't need to check whether l1
    // subsumes l2 because we are guaranteed here that l1 < l2, and (at least
    // in the cases we are interested in) a label may only subsume labels
    // created earlier (i.e. with a lower numerical value).
    if (__dfsan_label_info[l2].l1 == l1 ||
        __dfsan_label_info[l2].l2 == l1) {
      label = l2;
    } else {
      label =
        atomic_fetch_add(&__dfsan_last_label, 1, memory_order_relaxed) + 1;
      dfsan_check_label(label);
      __dfsan_label_info[label].l1 = l1;
      __dfsan_label_info[label].l2 = l2;
    }
    atomic_store(table_ent, label, memory_order_release);
  } else if (label == kInitializingLabel) {
    // Another thread is initializing the entry.  Wait until it is finished.
    do {
      internal_sched_yield();
      label = atomic_load(table_ent, memory_order_acquire);
    } while (label == kInitializingLabel);
  }
  return label;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
dfsan_label __dfsan_union_load(const dfsan_label *ls, uptr n) {
  dfsan_label label = ls[0];
  for (uptr i = 1; i != n; ++i) {
    dfsan_label next_label = ls[i];
    if (label != next_label)
      label = __dfsan_union(label, next_label);
  }
  return label;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
void __dfsan_unimplemented(char *fname) {
  if (flags().warn_unimplemented)
    Report("WARNING: DataFlowSanitizer: call to uninstrumented function %s\n",
           fname);
}

// Use '-mllvm -dfsan-debug-nonzero-labels' and break on this function
// to try to figure out where labels are being introduced in a nominally
// label-free program.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void __dfsan_nonzero_label() {
  if (flags().warn_nonzero_labels)
    Report("WARNING: DataFlowSanitizer: saw nonzero label\n");
}

// Indirect call to an uninstrumented vararg function. We don't have a way of
// handling these at the moment.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_vararg_wrapper(const char *fname) {
  Report("FATAL: DataFlowSanitizer: unsupported indirect call to vararg "
         "function %s\n", fname);
  Die();
}

// Like __dfsan_union, but for use from the client or custom functions.  Hence
// the equality comparison is done here before calling __dfsan_union.
SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
dfsan_union(dfsan_label l1, dfsan_label l2) {
  if (l1 == l2)
    return l1;
  return __dfsan_union(l1, l2);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
dfsan_label dfsan_create_label(const char *desc, void *userdata) {
  dfsan_label label =
    atomic_fetch_add(&__dfsan_last_label, 1, memory_order_relaxed) + 1;
  dfsan_check_label(label);
  __dfsan_label_info[label].l1 = __dfsan_label_info[label].l2 = 0;
  __dfsan_label_info[label].desc = desc;
  __dfsan_label_info[label].userdata = userdata;
  return label;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
void __dfsan_set_label(dfsan_label label, void *addr, uptr size) {
  for (dfsan_label *labelp = shadow_for(addr); size != 0; --size, ++labelp) {
    // Don't write the label if it is already the value we need it to be.
    // In a program where most addresses are not labeled, it is common that
    // a page of shadow memory is entirely zeroed.  The Linux copy-on-write
    // implementation will share all of the zeroed pages, making a copy of a
    // page when any value is written.  The un-sharing will happen even if
    // the value written does not change the value in memory.  Avoiding the
    // write when both |label| and |*labelp| are zero dramatically reduces
    // the amount of real memory used by large programs.
    if (label == *labelp)
      continue;

    *labelp = label;
  }
}

SANITIZER_INTERFACE_ATTRIBUTE
void dfsan_set_label(dfsan_label label, void *addr, uptr size) {
  __dfsan_set_label(label, addr, size);
}

SANITIZER_INTERFACE_ATTRIBUTE
void dfsan_add_label(dfsan_label label, void *addr, uptr size) {
  for (dfsan_label *labelp = shadow_for(addr); size != 0; --size, ++labelp)
    if (*labelp != label)
      *labelp = __dfsan_union(*labelp, label);
}

// Unlike the other dfsan interface functions the behavior of this function
// depends on the label of one of its arguments.  Hence it is implemented as a
// custom function.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
__dfsw_dfsan_get_label(long data, dfsan_label data_label,
                       dfsan_label *ret_label) {
  *ret_label = 0;
  return data_label;
}

SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
dfsan_read_label(const void *addr, uptr size) {
  if (size == 0)
    return 0;
  return __dfsan_union_load(shadow_for(addr), size);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
const struct dfsan_label_info *dfsan_get_label_info(dfsan_label label) {
  return &__dfsan_label_info[label];
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE int
dfsan_has_label(dfsan_label label, dfsan_label elem) {
  if (label == elem)
    return true;
  const dfsan_label_info *info = dfsan_get_label_info(label);
  if (info->l1 != 0) {
    return dfsan_has_label(info->l1, elem) || dfsan_has_label(info->l2, elem);
  } else {
    return false;
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
dfsan_has_label_with_desc(dfsan_label label, const char *desc) {
  const dfsan_label_info *info = dfsan_get_label_info(label);
  if (info->l1 != 0) {
    return dfsan_has_label_with_desc(info->l1, desc) ||
           dfsan_has_label_with_desc(info->l2, desc);
  } else {
    return internal_strcmp(desc, info->desc) == 0;
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE uptr
dfsan_get_label_count(void) {
  dfsan_label max_label_allocated =
      atomic_load(&__dfsan_last_label, memory_order_relaxed);

  return static_cast<uptr>(max_label_allocated);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
dfsan_dump_labels(int fd) {
  dfsan_label last_label =
      atomic_load(&__dfsan_last_label, memory_order_relaxed);

  for (uptr l = 1; l <= last_label; ++l) {
    char buf[64];
    internal_snprintf(buf, sizeof(buf), "%u %u %u ", l,
                      __dfsan_label_info[l].l1, __dfsan_label_info[l].l2);
    WriteToFile(fd, buf, internal_strlen(buf));
    if (__dfsan_label_info[l].l1 == 0 && __dfsan_label_info[l].desc) {
      WriteToFile(fd, __dfsan_label_info[l].desc,
                  internal_strlen(__dfsan_label_info[l].desc));
    }
    WriteToFile(fd, "\n", 1);
  }
}

// Returns the absolute Linux thread ID.
pid_t dfsan_get_tid() {
  return syscall( __NR_gettid );
}

// Returns the Linux thread ID relative to the base thread ID.
pid_t dfsan_get_relative_tid() {
  pid_t relative_tid = dfsan_get_tid() - base_tid;
  if ((unsigned)relative_tid >= kNumThreads) {
    Report("FATAL: DataFlowSanitizer: too many threads\n");
    Die();
  }
  return relative_tid;
}

// Returns a new block ID to be used in an assignment block.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE int
__dfsan_enter_assignment() {
  atomic_fetch_add(&__dfsan_last_execution, 1, memory_order_relaxed);
  pid_t rtid = dfsan_get_relative_tid();
  if (__dfsan_instruction_tracing[rtid]) {
    return atomic_fetch_add(&__dfsan_last_id, 1, memory_order_relaxed) + 1;
  } else {
    return __dfsan_region_id[rtid];
  }
}

// Prints a data-flow edge from the definer block of l to the given block ID.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_print_data_flow(dfsan_label l, int id) {
  const struct dfsan_label_info * info = dfsan_get_label_info(l);
  assert(info != NULL);
  // Non-base labels can be formed by the instrumentation code around loads and
  // stores, when the options -dfsan-combine-pointer-labels-on-load and
  // -dfsan-combine-pointer-labels-on-store are set to true (default). An
  // alternative implementation that would preserve the "only-base-labels"
  // invariant would be to treat loads and stores as first-class operations with
  // block IDs.
  if (info->l1 != 0) {
    __dfsan_print_data_flow(info->l1, id);
  }
  if (info->l2 != 0) {
    __dfsan_print_data_flow(info->l2, id);
  }
  void * data = info->userdata;
  assert(__dfsan_trace != NULL);
  // If l does not have a definer, assume it has been defined statically and
  // assign it the "source" region (0).
  // TODO: protect
  int definer = (data ? *((int*)data) : 0);
  if (definer != id) { // Avoid printing self-loops within trace blobs.
    fprintf(__dfsan_trace, "DF %d %d\n", definer, id);
  }
  // Print all tags (in instruction-level tracing).
  pid_t rtid = dfsan_get_relative_tid();
  if (__dfsan_instruction_tracing[rtid]) {
    struct tag* node = __dfsan_tags[rtid];
    while (node != NULL) {
      fprintf(__dfsan_trace, "BP %d TAG %s-%d-%d\n", id, node->key, node->group,
              node->instance);
      node = node->next;
    }
  }
  return;
}

// Creates a label with id as associated data.
dfsan_label __dfsan_create_id_label(int id) {
  // FIXME: improve this ugly thing, create a pool or something
  int * data = (int*) malloc(sizeof(int));
  data[0] = id;
  return dfsan_create_label("", data);
}

// Creates a new label l with the given definer.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
__dfsan_create_label_with_definer(int id) {
  // TODO: the overhead can be reduced by making the client fetch the relative
  // thread ID once and passing it as argument to all subsequent functions.
  pid_t rtid = dfsan_get_relative_tid();
  if (__dfsan_instruction_tracing[rtid]) {
    return __dfsan_create_id_label(id);
  } else {
    return __dfsan_region_label[rtid];
  }
}

// Prints a property of the given block ID.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_print_block_property(int id, const char * key, const char * value) {
  if (!__dfsan_instruction_tracing[dfsan_get_relative_tid()]) return;
  assert(__dfsan_trace != NULL);
  fprintf(__dfsan_trace, "BP %d %s %s\n", id, key, value);
}

// Prints a property of the given (static) instruction ID.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_print_instruction_property(const char * id, const char * key,
                                   const char * value) {
  if (!__dfsan_instruction_tracing[dfsan_get_relative_tid()]) return;
  // TODO: keep a set of visited instructions, avoid printing twice.
  assert(__dfsan_trace != NULL);
  fprintf(__dfsan_trace, "IP %s %s %s\n", id, key, value);
}

// Prints a property that holds for the entire region of the given block ID.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_print_region_property(int id, const char * key, const char * value) {
  if (__dfsan_instruction_tracing[dfsan_get_relative_tid()]) return;
  assert(__dfsan_trace != NULL);
  fprintf(__dfsan_trace, "BP %d %s %s\n", id, key, value);
}

// Creates a region and defines its properties.
dfsan_label __dfsan_create_region(int id, const char *name) {
  dfsan_label region_label = __dfsan_create_id_label(id);
  fprintf(__dfsan_trace, "BP %d INSTRUCTION %s\n", id, name);
  fprintf(__dfsan_trace, "IP %s NAME %s\n", name, name);
  fprintf(__dfsan_trace, "IP %s REGION TRUE\n", name);
  return region_label;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
dfsan_trace_region(const char *name) {
  int id = atomic_fetch_add(&__dfsan_last_id, 1, memory_order_relaxed) + 1;
  dfsan_label region_label = __dfsan_create_region(id, name);
  // __dfsan_last_id is the ID of the next trace region, not to be incremented
  // until __dfsan_instruction_tracing is set to 1 again.
  pid_t rtid = dfsan_get_relative_tid();
  __dfsan_instruction_tracing[rtid] = 0;
  __dfsan_region_id[rtid] =  id;
  __dfsan_region_label[rtid] =  region_label;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
dfsan_trace_instructions() {
  __dfsan_instruction_tracing[dfsan_get_relative_tid()] = 1;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
dfsan_begin_tagging(const char *t) {
  tag_counter i =
    atomic_fetch_add(&__dfsan_last_tag_instance, 1, memory_order_relaxed) + 1;
  pid_t rtid = dfsan_get_relative_tid();
  assert(!exists_tag(&__dfsan_tags[rtid], t));
  struct tag* tag = find_tag(&__dfsan_tag_groups[rtid], t);
  // If the group of this tag is not yet registered, assume it is 0.
  tag_counter g = tag == NULL ? 0 : tag->group;
  insert_tag(&__dfsan_tags[rtid], t, g, i);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
dfsan_end_tagging(const char *t) {
  pid_t rtid = dfsan_get_relative_tid();
  remove_tag(&__dfsan_tags[rtid], t);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
dfsan_new_group(const char *t) {
  pid_t rtid = dfsan_get_relative_tid();
  increment_tag_group(&__dfsan_tag_groups[rtid], t);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE int
dfsan_get_execution_count(void) {
  return atomic_load(&__dfsan_last_execution, memory_order_relaxed);
}

// Opens trace file and sets up the "source" region.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_open_trace() {
  __dfsan_trace = fopen("trace", "a");
  assert(__dfsan_trace != NULL);
  __dfsan_create_region(0, "source");
  // By convention, we define the source region as impure and non-commutative.
  fprintf(__dfsan_trace, "IP source IMPURE TRUE\n");
  fprintf(__dfsan_trace, "IP source NONCOMMUTATIVE TRUE\n");
  // Set the base thread ID to the ID of the initial thread.
  base_tid = dfsan_get_tid();
  // Start tracing at instruction level by default, initialize active tag lists.
  for (pid_t rtid = 0; (unsigned)rtid < kNumThreads; rtid++) {
    __dfsan_instruction_tracing[rtid] = 1;
    __dfsan_tags[rtid] = NULL;
  }
}

// Closes trace file.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_close_trace() {
  int ret = fclose(__dfsan_trace);
  assert(ret == 0);
}

// Emits a report.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_report(const char * report) {
  Report("NOTE: DataFlowSanitizer: %s\n", report);
}

void Flags::SetDefaults() {
#define DFSAN_FLAG(Type, Name, DefaultValue, Description) Name = DefaultValue;
#include "dfsan_flags.inc"
#undef DFSAN_FLAG
}

static void RegisterDfsanFlags(FlagParser *parser, Flags *f) {
#define DFSAN_FLAG(Type, Name, DefaultValue, Description) \
  RegisterFlag(parser, #Name, Description, &f->Name);
#include "dfsan_flags.inc"
#undef DFSAN_FLAG
}

static void InitializeFlags() {
  SetCommonFlagsDefaults();
  flags().SetDefaults();

  FlagParser parser;
  RegisterCommonFlags(&parser);
  RegisterDfsanFlags(&parser, &flags());
  parser.ParseString(GetEnv("DFSAN_OPTIONS"));
  InitializeCommonFlags();
  if (Verbosity()) ReportUnrecognizedFlags();
  if (common_flags()->help) parser.PrintFlagDescriptions();
}

static void InitializePlatformEarly() {
  AvoidCVE_2016_2143();
#ifdef DFSAN_RUNTIME_VMA
  __dfsan::vmaSize =
    (MostSignificantSetBitIndex(GET_CURRENT_FRAME()) + 1);
  if (__dfsan::vmaSize == 39 || __dfsan::vmaSize == 42 ||
      __dfsan::vmaSize == 48) {
    __dfsan_shadow_ptr_mask = ShadowMask();
  } else {
    Printf("FATAL: DataFlowSanitizer: unsupported VMA range\n");
    Printf("FATAL: Found %d - Supported 39, 42, and 48\n", __dfsan::vmaSize);
    Die();
  }
#endif
}

static void dfsan_fini() {
  if (internal_strcmp(flags().dump_labels_at_exit, "") != 0) {
    fd_t fd = OpenFile(flags().dump_labels_at_exit, WrOnly);
    if (fd == kInvalidFd) {
      Report("WARNING: DataFlowSanitizer: unable to open output file %s\n",
             flags().dump_labels_at_exit);
      return;
    }

    Report("INFO: DataFlowSanitizer: dumping labels to %s\n",
           flags().dump_labels_at_exit);
    dfsan_dump_labels(fd);
    CloseFile(fd);
  }
}

static void dfsan_init(int argc, char **argv, char **envp) {
  InitializeFlags();

  InitializePlatformEarly();

  if (!MmapFixedNoReserve(ShadowAddr(), UnusedAddr() - ShadowAddr()))
    Die();

  // Protect the region of memory we don't use, to preserve the one-to-one
  // mapping from application to shadow memory. But if ASLR is disabled, Linux
  // will load our executable in the middle of our unused region. This mostly
  // works so long as the program doesn't use too much memory. We support this
  // case by disabling memory protection when ASLR is disabled.
  uptr init_addr = (uptr)&dfsan_init;
  if (!(init_addr >= UnusedAddr() && init_addr < AppAddr()))
    MmapFixedNoAccess(UnusedAddr(), AppAddr() - UnusedAddr());

  InitializeInterceptors();

  // Register the fini callback to run when the program terminates successfully
  // or it is killed by the runtime.
  Atexit(dfsan_fini);
  AddDieCallback(dfsan_fini);

  __dfsan_label_info[kInitializingLabel].desc = "<init label>";
}

#if SANITIZER_CAN_USE_PREINIT_ARRAY
__attribute__((section(".preinit_array"), used))
static void (*dfsan_init_ptr)(int, char **, char **) = dfsan_init;
#endif
