/* SPDX-License-Identifier: BSD-2-Clause
 * Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <inttypes.h>
#include <stdbool.h>
#include <string.h>

#include "cuckoohash.h"

#ifndef ARRAYOF
# define ARRAYOF(_a)     (sizeof(_a)/sizeof(_a[0]))
#endif


static void
usage(const char *prog)
{
        fprintf(stderr, "%s [-n nb] [-c ctx_size] [-s] [-l]\n", prog);
}

int
main(int ac,
     char **av)
{
        int opt;
        unsigned nb = CUCKOO_NB_ENTRIES_MIN + 1;
        bool do_speed_test = false;
        bool do_analyze = false;
        bool do_unit = false;
        unsigned ctx_size = 5;	/* 1~8 default:5 */
        unsigned flags = 0;

        while ((opt = getopt(ac, av, "c:n:slua")) != -1) {

                switch (opt) {
                case 'a':
                        do_analyze = true;
                        break;
                case 'c':
                        ctx_size = atoi(optarg);
                        break;
                case 'n':
                        nb = atoi(optarg);
                        break;
                case 's':
                        do_speed_test = true;
                        break;
                case 'l':
                        flags |= CUCKOO_DISABLE_FLAG(CUCKOO_DISABLE_LIST);
                        break;
                case 'u':
                        do_unit = true;
                        break;
                default:
                        usage(av[0]);
                        exit(0);
                }
        }
        fprintf(stdout, "Memory size:%zu\n", cuckoo_sizeof(nb));
        cuckoo_test(nb, ctx_size, do_speed_test, do_analyze, do_unit, flags);

        return 0;
}
