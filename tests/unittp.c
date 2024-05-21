/* SPDX-License-Identifier: BSD-2-Clause
 * Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
 *
 * BSD 2-Clause License (https://www.opensource.org/licenses/bsd-license.php)
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *    * Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.
 *    * Redistributions in binary form must reproduce the above copyright
 *      notice, this list of conditions and the following disclaimer in
 *      the documentation and/or other materials provided with the
 *      distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <sys/mman.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <inttypes.h>
#include <stdlib.h>

#if defined(ENABLE_PAPI)
# include <papi.h>
#endif

#include "tinyallocator.h"
#include "cuckoohash.h"

/***************************************************************************************************
 * test code
 ***************************************************************************************************/
#ifndef ARRAYOF
# define ARRAYOF(_a)     (sizeof(_a)/sizeof(_a[0]))
#endif

#ifndef SWAP
# define SWAP(a,b) do { typeof(a) _c = (a); (a) = (b); (b) = _c;} while (0)
#endif

/*
 * 48 + 8 bytes
 */
union test_key_u {
        uint8_t data[48 + 64];
        uint32_t d32[12 + 16];
        uint64_t d64[ 6 +  8];
};

struct user_data_s {
        const union test_key_u *key;
        uint64_t something;
};


/*
 * Read Timestamp Counter (x86 only)
 */
static inline uint64_t
rdtsc(void)
{
        return __builtin_ia32_rdtsc();
}

static int
user_data_init(void *p,
               const void *k)
{
        static uint64_t some = 0;

        struct user_data_s *user = p;
        user->key = k;
        user->something = some++;
        return 0;
}

static void
speed_test_hash_bulk(struct mem_root_s *mem_root,
                     struct cuckoo_hash_s *cuckoo,
                     union test_key_u **key_pp,
                     unsigned nb)
{
        uint64_t tsc;
        union cuckoo_hash_u *hash;

        fprintf(stdout, "%s:%d nb:%u\n", __func__, __LINE__, nb);

        hash = TMA_alloc(mem_root, sizeof(*hash) * nb);
        if (hash) {
                for (unsigned i = 0; cuckoo_calchash_handlers[i].name; i++) {
                        cuckoo_calkhash_set(cuckoo, cuckoo_calchash_handlers[i].calc_hash);
                        tsc = rdtsc();
                        cuckoo_hash_bulk(cuckoo, (const void * const *) key_pp, hash, nb);
                        tsc = rdtsc() - tsc;
                        fprintf(stdout, "%s speed %0.2f tsc/key\n",
                                cuckoo_calchash_handlers[i].name,
                                (double) tsc / nb);
                }

                TMA_free(mem_root, hash);
        }
}

static inline int
test_32x16(void)
{
        uint32_t val[16];
        int ret = 0;

        for (unsigned i = 0; i < ARRAYOF(val); i++)
                val[i] = i;
        for (unsigned i = 0; i < ARRAYOF(val); i++) {
                uint64_t flags[8];

                for (unsigned j = 0; cuckoo_find_handlers[j].name; j++) {
                        flags[j] = cuckoo_find_handlers[j].find_32x16(val, i);
                        if (j > 0) {
                                if (flags[j] != flags[0]) {
                                        fprintf(stdout, "%uth Bad %s %"PRIx64"->%"PRIx64"\n",
                                                i, cuckoo_find_handlers[j].name,
                                                flags[0], flags[j]);
                                        ret = -1;
                                }
                        }
                }
        }
        return ret;
}

#if 0
struct test_s {
        struct cuckoo_hash_s cuckoo;
        uint32_t idx[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_bucket_s bk[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_node_s node[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_find_ctx_s ctx [CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        uint64_t hits[1024];
};

static void
unit_test(struct mem_root_s *mem_root)
{
        struct test_s *tbl = TMA_alloc(mem_root, sizeof(*tbl));
        if (tbl) {
                struct cuckoo_hash_s *cuckoo = &tbl->cuckoo;
                unsigned key_len = 0;
                unsigned node_size = sizeof(struct cuckoo_node_s) + key_len;
                uint64_t tsc;
                unsigned cnt = 0;

                memset(tbl, 0, sizeof(*tbl));

                IDX_POOL_INIT(&cuckoo->idx_pool, tbl->idx, ARRAYOF(tbl->idx));
                IDX_TBL_INIT(&cuckoo->bk_tbl, tbl->bk, ARRAYOF(tbl->bk), ARRAYOF(tbl->bk) - 1);
                IDX_GEN_TBL_INIT(&cuckoo->node_tbl, tbl->node, node_size, ARRAYOF(tbl->node));

                for (unsigned i = 0; i < ARRAYOF(tbl->bk); i++) {
                        struct cuckoo_bucket_s *bk = &tbl->bk[i];

                        for (unsigned j = 0; j < CUCKOO_BUCKET_ENTRY_SZ; j++) {
                                bk->hval[j] = j;
                                bk->idx[j] = j;
                        }
                }

                for (unsigned k = 0; k < CUCKOO_BUCKET_ENTRY_SZ; k++) {
                        struct cuckoo_find_ctx_s *ctx = &tbl->ctx[k];

                        ctx->bk[0] = bucket_ptr(cuckoo, k);
                        ctx->bk[1] = bucket_ptr(cuckoo, k + CUCKOO_BUCKET_ENTRY_SZ);
                }

                /* single test */
                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < ARRAYOF(tbl->bk); j++) {
                                struct cuckoo_bucket_s *bk = &tbl->bk[j];

                                tbl->hits[i] += GENERIC_find_hval_in_bucket(cuckoo, bk, 1);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "Generic single speed %0.2f tsc/bk\n", (double) tsc / cnt);

                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < ARRAYOF(tbl->bk); j++) {
                                struct cuckoo_bucket_s *bk = &tbl->bk[j];

                                tbl->hits[i] += SSE41_find_hval_in_bucket(cuckoo, bk, 1);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "SSE41 single speed %0.2f tsc/bk\n", (double) tsc / cnt);

                /* single test */
                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < ARRAYOF(tbl->bk); j++) {
                                struct cuckoo_bucket_s *bk = &tbl->bk[j];

                                tbl->hits[i] += AVX2_find_hval_in_bucket(cuckoo, bk, 1);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "AVX2 single speed %0.2f tsc/bk\n", (double) tsc / cnt);

                TMA_free(mem_root, tbl);
        }
}
#endif

static const uint32_t HVAL[] = {
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
};

static union cuckoo_hash_u
test_hash(const void *key,
          size_t key_len,
          uint32_t mask)
{
        const uint32_t *d32 = key;
        union cuckoo_hash_u hash;
        uint32_t v = d32[0];
        (void) key_len;

        mask = 15;

        hash.val32[1] = HVAL[v % (mask + 1)];
        hash.val32[0] = v / mask;
#if 0
        fprintf(stdout, "%s key:%x mask:%u hash[0]:%08x hash[1]:%08x xor:%08x\n",
                __func__, v, mask, hash.val32[0], hash.val32[1], hash.val32[0] ^ hash.val32[1]);
#endif
        return hash;
}

static void
random_key(union test_key_u **key_pp,
           unsigned nb)
{
        for (unsigned i = 0; i < nb; i++) {
                unsigned r = (unsigned) random() % nb;
                SWAP(key_pp[i], key_pp[r]);
        }
}

static void
random_user(struct user_data_s **user_pp,
            unsigned nb)
{
        for (unsigned i = 0; i < nb; i++) {
                unsigned r = (unsigned) random() % nb;
                SWAP(user_pp[i], user_pp[r]);
        }
}

static union test_key_u **
init_key(struct mem_root_s *mem_root,
         unsigned nb)
{
        size_t sz = sizeof(union test_key_u *) + sizeof(union test_key_u);

        union test_key_u ** array_p = TMA_alloc(mem_root, nb * sz);
        union test_key_u * array = (union test_key_u *) &array_p[nb];
        for (unsigned i = 0; i < nb; i++)
                array_p[i] = &array[i];

        for (unsigned i = 0; i < ARRAYOF(array->d32); i++) {
                random_key(array_p, nb);
                for (unsigned j = 0; j < nb; j++)
                        array_p[j]->d32[i] = (unsigned) random();
        }
        random_key(array_p, nb);

        return array_p;
}

static union cuckoo_hash_u
same_hash(const void *key,
          size_t key_len,
          uint32_t mask)
{
        union cuckoo_hash_u hash;
        (void) key;
        (void) mask;
        (void) key_len;

        hash.val32[1] = 1;
        hash.val32[0] = 0;

        return hash;
}

static int
walk_countup(struct cuckoo_hash_s *cuckoo,
             void *user,
             void *arg)
{
        unsigned *cnt_p = arg;
        char msg[80];
        int ret = 0;
        struct cuckoo_node_s *n = cuckoo_node(cuckoo, user);

        *cnt_p += 1;
        if (*cnt_p > cuckoo_used_num(cuckoo))
                ret = -1;

        snprintf(msg, sizeof(msg), "walk %d th", *cnt_p);
        cuckoo_node_dump(cuckoo, stdout, msg, n);

        snprintf(msg, sizeof(msg), "walk %d th current", *cnt_p);
        cuckoo_bucket_dump(cuckoo, stdout, msg, cuckoo_current_bucket(cuckoo, n));

        snprintf(msg, sizeof(msg), "walk %d th another", *cnt_p);
        cuckoo_bucket_dump(cuckoo, stdout, msg, cuckoo_another_bucket(cuckoo, n));

        fprintf(stdout, "\n");
        return ret;
}

static void
dump_all(struct cuckoo_hash_s *cuckoo)
{
        unsigned cnt;
        int n;

        cuckoo_dump(cuckoo, stdout, "All dump");

        cnt = 0;
        n = cuckoo_walk(cuckoo, walk_countup, &cnt);
        if (n)
                fprintf(stdout, "%s:%u unmatched counter n:%d cnt:%d\n",
                        __func__, __LINE__, n, cuckoo_used_num(cuckoo));
        if (cnt != cuckoo_used_num(cuckoo)) {
                char msg[256];
                snprintf(msg, sizeof(msg), "%s:%d unmatched counter. cnt:%u used:%u",
                         __func__, __LINE__, cnt, cuckoo_used_num(cuckoo));
                cuckoo_dump(cuckoo, stdout, msg);
        }
}

static int
single_add_del_test(struct cuckoo_hash_s *cuckoo,
                    union test_key_u **key_array,
                    unsigned nb)
{
        int ret = -1;
        union test_key_u *key = key_array[0];
        cuckoo_hash_func_t calk_hash = cuckoo_calkhash_get(cuckoo);
        struct user_data_s *user;

        fprintf(stdout, "\n%s start %u\n\n", __func__, nb);

        cuckoo_calkhash_set(cuckoo, test_hash);

        fprintf(stdout, "\nADD\n");

        user = cuckoo_find_oneshot(cuckoo, key, true, true);
        if (user) {
                struct cuckoo_bucket_s *bk_0, *bk_1;
                struct cuckoo_node_s *node = cuckoo_node(cuckoo, user);
                struct user_data_s *found;

                if (user->key != key) {
                        fprintf(stdout, "%s:%d mismatched key.\n", __func__, __LINE__);
                        goto end;
                }
                user->key = cuckoo_key(cuckoo, user);

                cuckoo_key_dump(cuckoo, stdout, "input key (ADD ok)", key);
                cuckoo_key_dump(cuckoo, stdout, "user key (ADD ok)", user->key);

                cuckoo_node_dump(cuckoo, stdout, "node (ADD ok)", node);

                bk_0 = cuckoo_current_bucket(cuckoo, node);
                bk_1 = cuckoo_another_bucket(cuckoo, node);

                cuckoo_bucket_dump(cuckoo, stdout, "ADD ok current", bk_0);
                cuckoo_bucket_dump(cuckoo, stdout, "ADD ok another", bk_1);
                cuckoo_dump(cuckoo, stdout, "ADD ok");

                if (cuckoo_verify(cuckoo, user, key)) {
                        fprintf(stdout, "%s:%d verify failed on add\n", __func__, __LINE__);
                        goto end;
                }

                if (cuckoo_flipflop(cuckoo, node)) {
                        fprintf(stdout, "%s:%d FlipFlop ng\n", __func__, __LINE__);
                        goto end;
                }

                cuckoo_bucket_dump(cuckoo, stdout, "After FlipFlop current",
                                   cuckoo_current_bucket(cuckoo, node));
                cuckoo_bucket_dump(cuckoo, stdout, "After FlipFlop another",
                                   cuckoo_another_bucket(cuckoo, node));

                if (bk_1 != cuckoo_current_bucket(cuckoo, node) ||
                    bk_0 != cuckoo_another_bucket(cuckoo, node)) {
                        fprintf(stdout, "%s:%d failed on FlipFlop\n",
                                __func__, __LINE__);
                        goto end;
                }
                fprintf(stdout, "%s:%d FlipFlop ok\n", __func__, __LINE__);

                cuckoo_node_dump(cuckoo, stdout, "After FlipFlop", node);
                cuckoo_dump(cuckoo, stdout, "After FlipFlop");

                found = cuckoo_find_oneshot(cuckoo, key, false, false);
                if (user != found) {
                        fprintf(stderr, "%s:%d mismatched user.\n", __func__, __LINE__);
                        goto end;
                }

                cuckoo_del_oneshot(cuckoo, user);

                cuckoo_node_dump(cuckoo, stdout, "After free", node);
                cuckoo_bucket_dump(cuckoo, stdout, "After free current", bk_1);
                cuckoo_bucket_dump(cuckoo, stdout, "After free another", bk_0);
                cuckoo_dump(cuckoo, stdout, "After free Cache");

                ret = 0;
        } else {
                fprintf(stdout, "%s:%d ADD ng\n", __func__, __LINE__);
        }

 end:
        fprintf(stdout, "\n");
        dump_all(cuckoo);
        fprintf(stdout, "\n%s end %d\n\n", __func__, ret);
        cuckoo_calkhash_set(cuckoo, calk_hash);

        return ret;
}

/*
 * same hash key
 */
static int
collision_test(struct cuckoo_hash_s *cuckoo,
               union test_key_u **key,
               unsigned nb)
{

        int ret = -1;
        struct user_data_s *user[CUCKOO_BUCKET_ENTRY_SZ + 1];
        struct cuckoo_bucket_s *bk[4];
        cuckoo_hash_func_t calk_hash = cuckoo_calkhash_get(cuckoo);
        struct cuckoo_node_s *node;
        struct cuckoo_node_s *last;

        fprintf(stdout, "\n%s start %u\n", __func__, nb);

        cuckoo_reset(cuckoo);
        cuckoo_calkhash_set(cuckoo, same_hash);

        for (unsigned i = 0; i < ARRAYOF(user); i++) {
                user[i] = cuckoo_find_oneshot(cuckoo, key[i], true, true);
                if (!user[i]) {
                        fprintf(stdout, "%s:%d failed to ADD %u\n", __func__, __LINE__, i);
                        goto end;
                }
                if (cuckoo_verify(cuckoo, user[i], key[i])) {
                        fprintf(stdout, "%s:%d failed to verify %u\n", __func__, __LINE__, i);
                        goto end;
                }
        }

        node = cuckoo_node(cuckoo, user[0]);
        last = cuckoo_node(cuckoo, user[CUCKOO_BUCKET_ENTRY_SZ]);
        bk[0] = cuckoo_current_bucket(cuckoo, node);
        bk[1] = cuckoo_another_bucket(cuckoo, node);
        bk[2] = cuckoo_current_bucket(cuckoo, last);
        bk[3] = cuckoo_another_bucket(cuckoo, last);

        if (0 != cuckoo_bk_empty_nb(cuckoo, bk[0]) ||
            (CUCKOO_BUCKET_ENTRY_SZ - 1) != cuckoo_bk_empty_nb(cuckoo, bk[1])) {
                cuckoo_bucket_dump(cuckoo, stdout, "current", bk[0]);
                cuckoo_bucket_dump(cuckoo, stdout, "another", bk[1]);

                fprintf(stdout, "%s:%d invalid bucket\n", __func__, __LINE__);
                goto end;
        }

        if (bk[0] != bk[3] || bk[1] != bk[2]) {
                fprintf(stdout, "%s:%d mismatched bk0123: %u %u %u %u\n",
                        __func__, __LINE__,
                        cuckoo_bucket_idx(cuckoo, bk[0]),
                        cuckoo_bucket_idx(cuckoo, bk[1]),
                        cuckoo_bucket_idx(cuckoo, bk[2]),
                        cuckoo_bucket_idx(cuckoo, bk[3]));
                goto end;
        }

        if (!cuckoo_flipflop(cuckoo, last)) {
                fprintf(stdout, "%s:%d Must be failed FlipFlop.\n", __func__, __LINE__);
                goto end;
        }
        if (cuckoo_flipflop(cuckoo, node)) {
                fprintf(stdout, "%s:%d failed FlipFlop.\n", __func__, __LINE__);
                goto end;
        }
        if (cuckoo_flipflop(cuckoo, last)) {
                 fprintf(stdout, "%s:%d failed FlipFlop.\n", __func__, __LINE__);
                goto end;
        }

        cuckoo_bucket_dump(cuckoo, stdout, "current", cuckoo_current_bucket(cuckoo, node));
        cuckoo_bucket_dump(cuckoo, stdout, "another", cuckoo_another_bucket(cuckoo, node));

        ret = 0;
 end:
        fprintf(stdout, "%s ret:%d\n\n", __func__, ret);
        cuckoo_calkhash_set(cuckoo, calk_hash);

        return ret;
}


struct verify_s {
        union test_key_u **key_pp;
        unsigned idx;
};

static int
verify_cb(struct cuckoo_hash_s *cuckoo,
          void *user,
          void *arg)
{
        struct verify_s *verify = arg;
        const union test_key_u *key = cuckoo_key(cuckoo, user);

        if (memcmp(key, verify->key_pp[verify->idx], sizeof(*key))) {
                fprintf(stderr, "%s:%d mismatched key %u\n",
                        __func__, __LINE__, verify->idx);
                return -1;
        }
        fprintf(stdout, "Ok %u\n", verify->idx);

        verify->idx += 1;
        return 0;
}

static int
verify_all(struct cuckoo_hash_s *cuckoo,
           union test_key_u **key_pp,
           unsigned nb)
{
        int ret = -1;
        struct verify_s arg;

        arg.key_pp = key_pp;
        arg.idx = 0;

        if (cuckoo_walk(cuckoo, verify_cb, &arg)) {
                fprintf(stderr, "%s:%d Bad walk\n", __func__, __LINE__);
                goto end;
        }
        fprintf(stderr, "%s:%d walk ok.\n", __func__, __LINE__);

        if (nb != cuckoo_used_num(cuckoo)) {
                fprintf(stderr, "mismatched NB. nb:%u num+%u\n", nb, cuckoo_used_num(cuckoo));
                goto end;
        }
        ret = 0;
 end:
        fprintf(stderr, "%s:%d ret:%d\n", __func__, __LINE__, ret);
        return ret;
}

static int
max_test(struct mem_root_s *mem_root,
         struct cuckoo_hash_s *cuckoo,
         union test_key_u **key_pp,
         unsigned nb)
{

        int ret = -1;
        struct user_data_s **user = TMA_alloc(mem_root, nb * sizeof(*user));
        struct user_data_s **n2 = TMA_alloc(mem_root, nb * sizeof(*n2));
        unsigned m, n;
        unsigned count;
        uint64_t tsc;
        unsigned del_nb;

        fprintf(stdout, "\n%s start %u\n", __func__, nb);

        cuckoo_reset(cuckoo);

        /* bulk without hash */
        n = cuckoo_find_bulk(cuckoo,
                             (const void * const *) key_pp,
                             nb, (void **) user, true, true);
        count = 0;
        for (unsigned i = 0; i < nb; i++) {
                if (user[i]) {
                        count++;
                }
        }

        if (n != count || n != cuckoo_used_num(cuckoo)) {
                fprintf(stdout, "%s:%d mismatched NB. n:%u num:%u count:%u\n",
                        __func__, __LINE__, n, cuckoo_used_num(cuckoo), count);
                dump_all(cuckoo);
                goto end;
        }

        fprintf(stdout, "%s success %u %.03f \n",
                __func__, n, (double) (cuckoo_used_num(cuckoo) * 100) / cuckoo_max_node(cuckoo));
        cuckoo_dump(cuckoo, stdout, "Bulk ");


        if (verify_all(cuckoo, key_pp, count)) {
                fprintf(stdout, "%s:%u verify failed\n", __func__, __LINE__);
                goto end;
        }

        if (count != cuckoo_used_num(cuckoo)) {
                fprintf(stdout, "Bulk(w) unmatched num: n=%u nb=%u count=%u\n",
                       n, cuckoo_used_num(cuckoo), count);
                goto end;
        }

        m = cuckoo_find_bulk(cuckoo, (const void * const *) key_pp,
                             nb, (void **) n2, true, true);
        if (n != m) {
                fprintf(stdout, "mismatched found keys m:%u n:%u\n", m, n);
                goto end;
        }
        for (unsigned i = 0; i < nb; i++) {
                if (user[i] != n2[i]) {
                        fprintf(stdout, "mismatched node %u\n", i);
                        goto end;
                }
        }

        fprintf(stdout, "start free\n");
        random_user(user, nb);
        tsc = rdtsc();
        del_nb = cuckoo_del_bulk(cuckoo, (void **) user, nb);
        if (del_nb != m) {
                fprintf(stdout, "mismatched deleted m:%u del:%u\n", m, del_nb);
                goto end;
        }
        fprintf(stdout, "delete %0.2f tsc/del\n", (double) (rdtsc() - tsc) / del_nb);

        ret = 0;
 end:
        cuckoo_dump(cuckoo, stdout, "Last dump");
        fprintf(stdout, "%s:%d ret:%d\n\n", __func__, __LINE__, ret);
        TMA_free(mem_root, user);
        TMA_free(mem_root, n2);
        return ret;
}

static double
speed_sub_sub(struct cuckoo_hash_s *cuckoo,
              union test_key_u **key_pp,
              unsigned nb,
              bool do_list)
{
        union test_key_u key[256] __attribute__((aligned(64)));
        struct user_data_s *user[256]__attribute__((aligned(64)));
        union test_key_u *key_p[256]__attribute__((aligned(64)));
        double tsc = 0;
        uint64_t start_cnt, end_cnt;
        uint64_t start_tsc, end_tsc;

        for (unsigned k = 0; k < ARRAYOF(key); k++)
                key_p[k] = &key[k];

        cuckoo_cnt_get(cuckoo, &start_cnt, &start_tsc);
        for (unsigned base = 0; base < nb; base += ARRAYOF(key)) {
                unsigned num;

                for (unsigned k = 0; k < ARRAYOF(key); k++)
                        memcpy(&key[k], key_pp[base + k], sizeof(union test_key_u));

                num = cuckoo_find_bulk(cuckoo, (const void * const *) key_p,
                                       ARRAYOF(key), (void **) user, true, do_list);
                if (ARRAYOF(key) != num) {
                        fprintf(stdout, "xxx Failure. num:%u base:%u\n", num, base);
                        goto end;
                }
        }
        cuckoo_cnt_get(cuckoo, &end_cnt, &end_tsc);

        tsc = (double) (end_tsc - start_tsc) / (double) (end_cnt - start_cnt);
 end:
         return tsc;
}

static int
speed_sub(struct cuckoo_hash_s *cuckoo,
          union test_key_u **key_pp,
          unsigned nb,
          bool do_list)
{
        double add = 0, search = 0;
        unsigned target_num = 256 * 1;
#if defined(ENABLE_PAPI)
        int ret;
        int EventSet = PAPI_NULL;
        int events[] = { PAPI_TLB_DM, PAPI_TOT_INS, PAPI_TOT_CYC, };
        long long values[4];
#endif
        cuckoo_reset(cuckoo);

#if defined(ENABLE_PAPI)
        ret = PAPI_library_init(PAPI_VER_CURRENT);
        if (ret < 0) {
                fprintf(stderr, "Failed to init PAPI lib. %s\n",
                        PAPI_strerror(ret));
                return -1;
        }

        ret = PAPI_create_eventset(&EventSet);
        if (ret != PAPI_OK) {
                fprintf(stderr, "Failed to create PAPI event set. %s\n",
                        PAPI_strerror(ret));
                return -1;
        }
        for (unsigned i = 0; i < ARRAYOF(events); i++) {
                ret = PAPI_add_event(EventSet, events[i]);
                if (ret != PAPI_OK) {
                        fprintf(stderr, "Failed to add PAPI events %u. %s\n",
                                i, PAPI_strerror(ret));
                        return -1;
                }
        }
        ret = PAPI_start(EventSet);
        if (ret != PAPI_OK) {
                fprintf(stderr, "Failed to start PAPI event set. %s\n",
                        PAPI_strerror(ret));
                return -1;
        }
#endif /* PAPI */

        for (unsigned i = 0; i < 64; i++) {
                random_key(key_pp, nb);
                cuckoo_reset(cuckoo);
                add += speed_sub_sub(cuckoo, key_pp, nb, do_list);

                random_key(key_pp, nb);
                search += speed_sub_sub(cuckoo, key_pp, target_num, do_list);
        }

#if defined(ENABLE_PAPI)
        ret = PAPI_stop(EventSet, values);
        if (ret != PAPI_OK) {
                fprintf(stderr, "Failed to stop PAPI event set. %s\n",
                        PAPI_strerror(ret));
                return -1;
        }
        PAPI_shutdown();
        fprintf(stdout, "IPC:%0.2f %lld\n",
                (double) values[1] / (double) values[2],
                values[0]);
#endif /* PAPI */

        fprintf(stdout, "bulk nb:%u add:find %0.2f - %0.2f tsc/key\n",
                nb,
                add / 64, search / 64);

        return 0;
}

static void
analyze_ctx_num(struct cuckoo_hash_s *cuckoo,
                union test_key_u **key_pp,
                unsigned nb)
{
        for (unsigned i = 0; i < 2; i++) {
                uint64_t best_tsc = UINT64_C(-1);
                unsigned best_nb = (unsigned) -1;

                for (unsigned ctx_nb = 1; ctx_nb < 9; ctx_nb++) {
                        uint64_t tsc, dummy;

                        cuckoo_ctxnb_set(cuckoo, ctx_nb);
                        cuckoo_reset(cuckoo);

                        random_key(key_pp, nb);
                        speed_sub_sub(cuckoo, key_pp, nb, true);

                        random_key(key_pp, nb);
                        speed_sub_sub(cuckoo, key_pp, nb, true);

                        cuckoo_cnt_get(cuckoo, &dummy, &tsc);
                        if (best_tsc > tsc) {
                                best_tsc = tsc;
                                best_nb = ctx_nb;
                        }
                        fprintf(stdout, "ctx_nb:%u\n", best_nb);
                }
        }
}

static int
speed_test(struct cuckoo_hash_s *cuckoo,
           union test_key_u **key_pp,
           unsigned nb,
           bool do_list)
{
       int ret = -1;

       nb = cuckoo_max_node(cuckoo);
       nb &= (unsigned) ~255;

       fprintf(stdout, "\n%s start %u\n", __func__, nb);
       if (!nb)
               goto end;

       for (unsigned i = 0; i < 4; i++) {
               ret = speed_sub(cuckoo, key_pp, nb, do_list);
               if (ret)
                       goto end;
       }

       cuckoo_dump(cuckoo, stdout, "speed");

 end:
       cuckoo_reset(cuckoo);

       return ret;
}


#define NUM_ACCESSES	1024
#define CACHELINE_SIZE  64

struct cacheline_s {
        volatile uint64_t val[16];
};

static inline uint64_t
measure_chunk(const struct cacheline_s *lines,
              unsigned *index,
              unsigned idx_sz)
{
        uint64_t start = rdtsc();
        for (unsigned i = 0; i < idx_sz; i++) {
                unsigned v = index[i];

                volatile uint64_t sink = lines[v].val[0];
                (void) sink;
        }
        return rdtsc() - start;
}

static int
measure_cache_clear(struct mem_root_s *mem_root,
                    unsigned nb_lines)
{
        struct cacheline_s *lines = TMA_alloc(mem_root, sizeof(*lines) * nb_lines);
        int ret = -1;
        if (lines) {
                for (unsigned i = 0; i < nb_lines; i++)
                        lines[i].val[0] = i;
                ret = 0;
                TMA_free(mem_root, lines);
        }
        return ret;
}

static int
measure_latency(struct mem_root_s *mem_root,
                unsigned nb_lines)
{
        struct cacheline_s *lines = TMA_alloc(mem_root, sizeof(*lines) * nb_lines);
        int ret = -1;

        if (lines) {
                unsigned index[256];
                uint64_t total_cycles = 0;

                for (unsigned i = 0; i < nb_lines; i++) {
                        lines[i].val[0] = i;
                }

                if (measure_cache_clear(mem_root, 262144 * 1.5))
                        goto end;

                for (unsigned i = 0; i < ARRAYOF(index); i++)
                        index[i] = (unsigned) rand() % nb_lines;

                total_cycles += measure_chunk(lines, index, ARRAYOF(index));

                printf("Average cache miss latency: nb:%u %f cycles\n",
                       nb_lines,
                       (double) total_cycles / (double) ARRAYOF(index));
                ret = 0;
        end:
                TMA_free(mem_root, lines);
        }
        return ret;
}

static void
measure_cache_miss_latency_tsc(struct mem_root_s *mem_root)
{
        unsigned nb_lines = 262144;
        int ret;

        do {
                ret = measure_latency(mem_root, nb_lines);
                nb_lines <<= 1;
        } while (!ret);
}

static int
mem_area_test(struct cuckoo_hash_s *cuckoo,
              unsigned nb,
              unsigned key_len)
{
        size_t sz = cuckoo_sizeof(nb, key_len);
        uint8_t *p = (uint8_t *) cuckoo_node_ptr(cuckoo, nb);

        size_t len = (size_t) (p - (uint8_t *) cuckoo);
        fprintf(stdout, "size:%zu len:%zu\n", sz, len);

        return !(sz == len);
}

int
cuckoo_test(unsigned nb,
            unsigned ctx_size,
            bool do_basic,
            bool do_speed_test,
            bool do_analyze,
            bool do_unit,
            bool do_mem,
            bool do_hp,
            bool do_list,
            unsigned flags)
{
        struct mem_root_s *mem_root = NULL;
        struct cuckoo_hash_s *cuckoo = NULL;
        struct user_data_s *user_array = NULL;
        size_t len;
        union test_key_u **key;
        cuckoo_hash_func_t hash_func = NULL;

#if 0
        hash_func = XXH_calc_hash;
#endif

        mem_root = TMA_create((size_t) 2 * 1024 * 1024 * 1024,
                              (size_t) 2 * 1024 * 1024,
                              do_hp);
        if (!mem_root) {
                fprintf(stderr, "no mempry\n");
                goto end;
        }

        len = cuckoo_sizeof(nb, sizeof(union test_key_u));
        fprintf(stdout, "nb:%u size:%zu %fMB\n", nb, len, (double) len/1024/1024);

        cuckoo = TMA_alloc(mem_root, len);
        user_array = TMA_alloc(mem_root, sizeof(*user_array) * nb);

        if (!cuckoo || !user_array) {
                fprintf(stderr, "no mempry\n");
                goto end;
        }

        cuckoo_init(cuckoo, nb, sizeof(union test_key_u), ctx_size,
                    hash_func,
                    user_data_init, user_array, sizeof(*user_array),
                    flags);

        cuckoo_dump(cuckoo, stdout, "Root");
        if (mem_area_test(cuckoo, nb, sizeof(union test_key_u))) {
                fprintf(stderr, "failed to test memory area.\n");
                goto end;
        }

        key = init_key(mem_root, nb);

        if (do_basic) {
                if (single_add_del_test(cuckoo, key, nb))
                        goto end;

                if (collision_test(cuckoo, key, nb))
                        goto end;

                if (max_test(mem_root, cuckoo, key, nb))
                        goto end;
        }

        if (do_speed_test) {
                if (speed_test(cuckoo, key, nb, do_list))
                        goto end;
        }

        if (do_analyze)
                analyze_ctx_num(cuckoo, key, nb);

        if (do_unit) {
                speed_test_hash_bulk(mem_root, cuckoo, key, nb);
#if 0
                unit_test(mem_root);
#endif
        }


 end:
        TMA_free(mem_root, user_array);
        TMA_free(mem_root, cuckoo);

        if (do_mem)
                measure_cache_miss_latency_tsc(mem_root);

        TMA_destroy(mem_root);
        return 0;
}



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
