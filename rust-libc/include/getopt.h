#ifndef _GETOPT_H
#define _GETOPT_H
#include <bits/features.h>

struct option {
    const char *name;
    int has_arg;
    int *flag;
    int val;
};

#define no_argument 0
#define required_argument 1
#define optional_argument 2

__BEGIN_DECLS
extern char *optarg;
extern int optind, opterr, optopt, optreset;
int getopt(int, char *const[], const char *);
int getopt_long(int, char *const[], const char *, const struct option *, int *);
int getopt_long_only(int, char *const[], const char *, const struct option *, int *);
__END_DECLS

#endif
