#ifndef _SEARCH_H
#define _SEARCH_H
#include <bits/features.h>

#define __NEED_size_t
#include <bits/alltypes.h>

typedef enum { FIND, ENTER } ACTION;
typedef enum { preorder, postorder, endorder, leaf } VISIT;

typedef struct entry {
    char *key;
    void *data;
} ENTRY;

struct hsearch_data {
    struct __tab *__tab;
    unsigned int __unused1;
    unsigned int __unused2;
};

struct qelem {
    struct qelem *q_forw;
    struct qelem *q_back;
    char q_data[1];
};

__BEGIN_DECLS
int hcreate(size_t);
void hdestroy(void);
ENTRY *hsearch(ENTRY, ACTION);
int hcreate_r(size_t, struct hsearch_data *);
void hdestroy_r(struct hsearch_data *);
int hsearch_r(ENTRY, ACTION, ENTRY **, struct hsearch_data *);

void insque(void *, void *);
void remque(void *);

void *lsearch(const void *, void *, size_t *, size_t, int (*)(const void *, const void *));
void *lfind(const void *, const void *, size_t *, size_t, int (*)(const void *, const void *));

void *tdelete(const void *__RESTRICT, void **__RESTRICT, int (*)(const void *, const void *));
void *tfind(const void *, void *const *, int (*)(const void *, const void *));
void *tsearch(const void *, void **, int (*)(const void *, const void *));
void twalk(const void *, void (*)(const void *, VISIT, int));
void tdestroy(void *, void (*)(void *));
__END_DECLS

#endif
