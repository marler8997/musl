#include <stddef.h>
#include "dynlink.h"
#include "errno.h"
#include "syscall.h"

#ifndef START
#define START "_dlstart"
#endif

#define SHARED

#include "crt_arch.h"

#define stdout 1
#define print_strlit(fd, msg) write(fd, msg, sizeof(msg) - 1);
static long write(int fd, char const* msg, unsigned length)
{
  return syscall_cp(SYS_write, fd, msg, length);
}

static unsigned strlen2(const char *s)
{
  unsigned i = 0;
  for (; s[i]; i++) { }
  return i;
}
static void string_reverse(char *start, char *limit)
{
  for (;;)
    {
      limit--;
      if (limit <= start)
        break;
      char temp = start[0];
      start[0] = limit[0];
      limit[0] = temp;
      start++;
    }
}
static char *sprint_unsigned(char *buffer, unsigned long i)
{
  if (i == 0) {
    buffer[0] = '0';
    return buffer + 1;
  }
  char *start = buffer;
  do {
    buffer[0] = (i % 10) + '0';
    buffer++;
    i /= 10;
  } while (i);
  string_reverse(start, buffer);
  return buffer;
}
static char *sprint_signed(char *buffer, long i)
{
  if (i < 0) {
    buffer[0] = '-';
    buffer++;
    i *= -1;
  }
  return sprint_unsigned(buffer, (unsigned long)i);
}

static int print_unsigned(int fd, unsigned long i)
{
  char buffer[50];
  char *end = sprint_unsigned(buffer, i);
  write(fd, buffer, end - buffer);
}
static int print_signed(int fd, long i)
{
  char buffer[50];
  char *end = sprint_signed(buffer, i);
  write(fd, buffer, end - buffer);
}

#define PROT_READ     0x01
#define PROT_WRITE    0x02
#define MAP_PRIVATE   0x02
#define MAP_ANONYMOUS 0x20
static void *mmap_alloc(size_t size)
{
  return (void*)syscall_cp(SYS_mmap, NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
}

hidden void _dlstart_c(size_t *sp, size_t *dynv)
{
  size_t aux[AUX_CNT], dyn[DYN_CNT];

  int argc = *sp;
  char **argv = (void *)(sp+1);
  char **envp = argv + (argc + 1);

  // TODO: detect if argv[0] is ourselves
  //       in that case we need to replace ourselves with the real
  //       loader rather than prefix argv with the new loader

  size_t envc = 0;
  for (; envp[envc]; envc++) { }

  size_t *auxv = (size_t*)(envp + envc + 1);

  for (int i=0; i<AUX_CNT; i++) aux[i] = 0;
  for (int i=0; auxv[i]; i+=2) if (auxv[i]<AUX_CNT)
                                 aux[auxv[i]] = auxv[i+1];
  size_t base;

#if DL_FDPIC
  struct fdpic_loadseg *segs, fakeseg;
  size_t j;
  if (dynv) {
    /* crt_arch.h entry point asm is responsible for reserving
     * space and moving the extra fdpic arguments to the stack
     * vector where they are easily accessible from C. */
    segs = ((struct fdpic_loadmap *)(sp[-1] ? sp[-1] : sp[-2]))->segs;
  } else {
    /* If dynv is null, the entry point was started from loader
     * that is not fdpic-aware. We can assume normal fixed-
     * displacement ELF loading was performed, but when ldso was
     * run as a command, finding the Ehdr is a heursitic: we
     * have to assume Phdrs start in the first 4k of the file. */
    base = aux[AT_BASE];
    if (!base) base = aux[AT_PHDR] & -4096;
    segs = &fakeseg;
    segs[0].addr = base;
    segs[0].p_vaddr = 0;
    segs[0].p_memsz = -1;
    Ehdr *eh = (void *)base;
    Phdr *ph = (void *)(base + eh->e_phoff);
    size_t phnum = eh->e_phnum;
    size_t phent = eh->e_phentsize;
    while (phnum-- && ph->p_type != PT_DYNAMIC)
      ph = (void *)((size_t)ph + phent);
    dynv = (void *)(base + ph->p_vaddr);
  }
#endif

  for (int i=0; i<DYN_CNT; i++) dyn[i] = 0;
  for (int i=0; dynv[i]; i+=2) if (dynv[i]<DYN_CNT)
                                 dyn[dynv[i]] = dynv[i+1];

#if DL_FDPIC
  for (int i=0; i<DYN_CNT; i++) {
    if (i==DT_RELASZ || i==DT_RELSZ) continue;
    if (!dyn[i]) continue;
    for (j=0; dyn[i]-segs[j].p_vaddr >= segs[j].p_memsz; j++);
    dyn[i] += segs[j].addr - segs[j].p_vaddr;
  }
  base = 0;

  const Sym *syms = (void *)dyn[DT_SYMTAB];

  {
    size_t *rel = (void *)dyn[DT_RELA];
    size_t rel_size = dyn[DT_RELASZ];
    for (; rel_size; rel+=3, rel_size-=3*sizeof(size_t)) {
      if (!IS_RELATIVE(rel[1], syms)) continue;
      for (j=0; rel[0]-segs[j].p_vaddr >= segs[j].p_memsz; j++);
      size_t *rel_addr = (void *)
        (rel[0] + segs[j].addr - segs[j].p_vaddr);
      if (R_TYPE(rel[1]) == REL_FUNCDESC_VAL) {
        *rel_addr += segs[rel_addr[1]].addr
          - segs[rel_addr[1]].p_vaddr
          + syms[R_SYM(rel[1])].st_value;
        rel_addr[1] = dyn[DT_PLTGOT];
      } else {
        size_t val = syms[R_SYM(rel[1])].st_value;
        for (j=0; val-segs[j].p_vaddr >= segs[j].p_memsz; j++);
        *rel_addr = rel[2] + segs[j].addr - segs[j].p_vaddr + val;
      }
    }
  }
#else
  /* If the dynamic linker is invoked as a command, its load
   * address is not available in the aux vector. Instead, compute
   * the load address as the difference between &_DYNAMIC and the
   * virtual address in the PT_DYNAMIC program header. */
  base = aux[AT_BASE];
  char is_loader;
  if (base) {
    is_loader = 1;
    print_strlit(stdout, "[elfenv] COMMAND_OR_LOADER? base is ");
    print_unsigned(stdout,base);
    print_strlit(stdout, "\n");
  } else {
    is_loader = 0;
    print_strlit(stdout, "[elfenv] COMMAND_OR_LOADER? base is 0!\n");
    size_t phnum = aux[AT_PHNUM];
    size_t phentsize = aux[AT_PHENT];
    Phdr *ph = (void *)aux[AT_PHDR];
    for (size_t i=phnum; i--; ph = (void *)((char *)ph + phentsize)) {
      if (ph->p_type == PT_DYNAMIC) {
        base = (size_t)dynv - ph->p_vaddr;
        break;
      }
    }
  }
  print_strlit(stdout, "[elfenv] is_loader: ");
  print_unsigned(stdout, is_loader);
  print_strlit(stdout, "\n");

  /* MIPS uses an ugly packed form for GOT relocations. Since we
   * can't make function calls yet and the code is tiny anyway,
   * it's simply inlined here. */
  if (NEED_MIPS_GOT_RELOCS) {
    size_t local_cnt = 0;
    size_t *got = (void *)(base + dyn[DT_PLTGOT]);
    for (size_t i=0; dynv[i]; i+=2) if (dynv[i]==DT_MIPS_LOCAL_GOTNO)
                                      local_cnt = dynv[i+1];
    for (size_t i=0; i<local_cnt; i++) got[i] += base;
  }

  {
    size_t *rel = (void *)(base+dyn[DT_REL]);
    size_t rel_size = dyn[DT_RELSZ];
    for (; rel_size; rel+=2, rel_size-=2*sizeof(size_t)) {
      if (!IS_RELATIVE(rel[1], 0)) continue;
      size_t *rel_addr = (void *)(base + rel[0]);
      *rel_addr += base;
    }
  }
  {
    size_t *rel = (void *)(base+dyn[DT_RELA]);
    size_t rel_size = dyn[DT_RELASZ];
    for (; rel_size; rel+=3, rel_size-=3*sizeof(size_t)) {
      if (!IS_RELATIVE(rel[1], 0)) continue;
      size_t *rel_addr = (void *)(base + rel[0]);
      *rel_addr = base + rel[2];
    }
  }
#endif

  print_strlit(stdout, "[elfenv] argc: ");
  print_unsigned(stdout, argc);
  print_strlit(stdout, "\n");
  for (unsigned i = 0; i < argc; i++) {
    print_strlit(stdout, "[elfenv] argv[");
    print_unsigned(stdout, i);
    print_strlit(stdout, "] = '");
    write(stdout, argv[i], strlen2(argv[i]));
    print_strlit(stdout, "'\n");
  }
  for (unsigned i = 0;; i++) {
    char *env = envp[i];
    if (!env)
      break;
    print_strlit(stdout, "[elfenv] ");
    write(stdout, env, strlen2(env));
    print_strlit(stdout, "\n");
  }
  if (argc < 1) {
    print_strlit(stdout, "[elfenv] Error: argc is ");
    print_signed(stdout, argc);
    print_strlit(stdout, "\n");
    syscall_cp(SYS_exit, 1);
  }
  char *elfprog = argv[0];
  print_strlit(stdout,"[elfenv] TODO: find real interpreter from '");
  write(stdout, elfprog, strlen2(elfprog));
  print_strlit(stdout, "'\n");

  const char *loader = "/nix/store/681354n3k44r8z90m35hm8945vsp95h1-glibc-2.27/lib/ld-linux-x86-64.so.2";
  print_strlit(stdout, "[elfenv] using hard-coded loader: '");
  write(stdout, loader, strlen2(loader));
  print_strlit(stdout, "'\n");

  char **new_argv = argv;
  int new_argc = argc;
  if (is_loader) {
    // add the loader to argv
    // TODO: probably be better to allocate on the stack
    //       rather than using a syscall to allocate memory here
    new_argv = (char**)mmap_alloc(sizeof(char*) * (argc + 2));
    /*
      print_strlit(stdout, "mmap_alloc returned: ");
      print_unsigned(stdout, (unsigned long)new_argv);
      print_strlit(stdout, "\n");
    */
    if (!new_argv) {
      int save_errno = errno;
      print_strlit(stdout, "[elfenv] Error: mmap failed, errno=");
      //print_signed(stdout, save_errno);
      syscall_cp(SYS_exit, 1);
    }
    new_argv[0] = (char*)loader;
    for (unsigned i = 0; i < argc; i++) {
      new_argv[i + 1] = argv[i];
    }
    new_argv[argc + 1] = NULL;
    new_argc++;
  } else {
    argv[0] = (char*)loader;
    new_argv = argv;
  }

  for (unsigned i = 0; i < new_argc; i++) {
    print_strlit(stdout, "[elfenv] new_argv[");
    print_unsigned(stdout, i);
    print_strlit(stdout, "] = '");
    write(stdout, new_argv[i], strlen2(new_argv[i]));
    print_strlit(stdout, "'\n");
  }


  print_strlit(stdout, "[elfenv] calling execve...\n");
  syscall_cp(SYS_execve, loader, new_argv, envp);
  {
    //int save_errno = errno;
    print_strlit(stdout, "Error: execve system call failed, errno=");
    print_signed(stdout, errno);
    print_strlit(stdout, "\n");
  }
  syscall_cp(SYS_exit, 1);
}
