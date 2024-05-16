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
        fprintf(stderr,
                "%s [-n nb] [-c ctx] [-s] [-l] [-b] [-m] [-u] [-g] [-d] [-4]\n"
                "-n nb	Number of elements\n"
                "-c ctx	Number of contexts\n"
                "-s	Speed Test\n"
                "-l	No Listing\n"
                "-b	Basic Test\n"
                "-m	Memory laytency\n"
                "-u	Unit Test\n"
                "-g	Hugepage mode\n"
                "-d	Debug mode\n"
                "-4     Disable SSE4.2\n"
                , prog);
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
        bool do_basic = false;
        bool do_mem = false;
        bool do_hp = false;
        bool do_list = true;
        unsigned ctx_size = 7;	/* 1~9 default:5 */
        unsigned flags = 0;

        while ((opt = getopt(ac, av, "c:n:sluabmhgd4")) != -1) {

                switch (opt) {
                case '4':
                        flags |= CUCKOO_DISABLE_FLAG(CUCKOO_DISABLE_SSE42);
                        break;
                case 'g':
                        do_hp = true;
                        break;
                case 'a':
                        do_analyze = true;
                        break;
                case 'b':
                        do_basic = true;
                        break;
                case 'c':
                        ctx_size = (unsigned) atoi(optarg);
                        break;
                case 'm':
                        do_mem = true;
                        break;
                case 'n':
                        nb = (unsigned) atoi(optarg);
                        break;
                case 's':
                        do_speed_test = true;
                        break;
                case 'l':
                        do_list = false;
                        break;
                case 'u':
                        do_unit = true;
                        break;
                case 'd':
                        flags |= CUCKOO_DISABLE_FLAG(CUCKOO_ENABLE_DEBUG);
                        break;
                case 'h':
                default:
                        usage(av[0]);
                        exit(0);
                }
        }

        cuckoo_test(nb, ctx_size, do_basic, do_speed_test, do_analyze, do_unit, do_mem, do_hp, do_list, flags);

        return 0;
}
