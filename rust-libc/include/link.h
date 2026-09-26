#ifndef _LINK_H
#define _LINK_H
#include <bits/features.h>
#include <elf.h>
#include <stddef.h>

#define ElfW(type) Elf64_##type

struct dl_phdr_info {
    Elf64_Addr dlpi_addr;
    const char *dlpi_name;
    const Elf64_Phdr *dlpi_phdr;
    Elf64_Half dlpi_phnum;
    unsigned long long dlpi_adds;
    unsigned long long dlpi_subs;
    size_t dlpi_tls_modid;
    void *dlpi_tls_data;
};

__BEGIN_DECLS
int dl_iterate_phdr(int (*)(struct dl_phdr_info *, size_t, void *), void *);
__END_DECLS

#endif
