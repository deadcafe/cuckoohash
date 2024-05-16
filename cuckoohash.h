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

/*
 * Spec:
 */

#ifndef _CUCKOOHASH_H_
#define _CUCKOOHASH_H_

#include <sys/types.h>
#include <stdint.h>
#include <stdbool.h>

#define CUCKOO_BUCKET_ENTRY_SZ	16
#define CUCKOO_NB_ENTRIES_MIN	(CUCKOO_BUCKET_ENTRY_SZ * CUCKOO_BUCKET_ENTRY_SZ * CUCKOO_BUCKET_ENTRY_SZ)

/*
 *
 */
enum cuckoo_opt_e {
        CUCKOO_ENABLE_DEBUG = 0,
        CUCKOO_DISABLE_SSE41,
        CUCKOO_DISABLE_SSE42,
        CUCKOO_DISABLE_AVX2,
        CUCKOO_DISABLE_AVX512,

        CUCKOO_DISABLE_NB,
};

#define CUCKOO_DISABLE_ALL		(unsigned) -1
#define	CUCKOO_DISABLE_FLAG(opt)	(1 << (opt))
#define CUCKOO_IS_DISABLE(flag, opt)	((flag) & CUCKOO_DISABLE_FLAG((opt)))

struct cuckoo_node_s;
struct cuckoo_bucket_s;

/**
 * @brief Calculates the hash value for a given key.
 *
 * Outputs two 32-bit hash values.
 * Each hash value must also differ when ANDed with the specified mask,
 * and must also differ from 0xffffffff.
 *
 * @param key Pointer to the cuckoo_key_s structure that contains the key.
 * @param mask value
 * @return cuckoo_hash_u 64bit hash value
 */
typedef union cuckoo_hash_u (*cuckoo_hash_func_t)(const void *key, unsigned len, uint32_t mask);

/**
 * @brief Function to initialize node
 *
 * @param node pointer
 * @param key
 * @param key_len
 * @return void
 */
typedef int (*cuckoo_user_initializer_t)(void *user_data, const void *key);

/**
 * @brief Generate cuckoo hashing table
 *
 * @param nb to the number of nodes.
 * @param ctx_size to the context number of pipeline.(1 - 8)
 * @param calc_hash to the hash calculater.
 * @param node_init to the node initialize.
 * @param key_len to the length of key.
 * @param opt_flags to the functional restriction flag.
 * @return cuckoo_hash_s pointer. Use free when destroying.
 */
extern struct cuckoo_hash_s *cuckoo_create(unsigned nb,
                                           unsigned key_len,
                                           unsigned ctx_size,
                                           cuckoo_hash_func_t calc_hash,
                                           cuckoo_user_initializer_t user_init,
                                           void *user_array,
                                           unsigned user_len,
                                           unsigned opt_flags);

/**
 * @brief Initialize cuckoo hashing table
 *
 * @param cuckoo to the hashing table pointer.
 * @param nb to the number of nodes.
 * @param ctx_size to the context number of pipeline.(1 - 8)
 * @param calc_hash to the hash calculater.
 * @param node_init to the node initialize.
 * @param key_len to the length of key.
 * @param opt_flags to the functional restriction flag.
 * @return success then Zero
 */
extern int cuckoo_init(struct cuckoo_hash_s *cuckoo,
                       unsigned nb,
                       unsigned key_len,
                       unsigned ctx_size,
                       cuckoo_hash_func_t calc_hash,
                       cuckoo_user_initializer_t user_init,
                       void *user_array,
                       unsigned user_len,
                       unsigned opt_flags);
/**
 * @brief Reset cucko hashing table.
 *
 * @param cuckoo to the hashing table pointer.
 * @return void
 */
extern void cuckoo_reset(struct cuckoo_hash_s *cuckoo);

/**
 * @brief Find hashing table size.
 *
 * @param nb to the number of nodes.
 * @return size_t
 */
extern size_t cuckoo_sizeof(unsigned nb, unsigned ken_len);

/**
 * @brief Number of nodes in use
 *
 * @param cuckoo to the hashing table pointer.
 * @return Number of nodes
 */
extern unsigned cuckoo_used_num(const struct cuckoo_hash_s *cuckoo);

/**
 * @brief Number of Max nodes
 *
 * @param cuckoo to the hashing table pointer.
 * @return Number of MAX nodes
 */
extern unsigned cuckoo_max_node(const struct cuckoo_hash_s *cuckoo);

/**
 * @brief Number of unused nodes
 *
 * @param cuckoo to the hashing table pointer.
 * @return Number of unused nodes
 */
extern unsigned cuckoo_empty_num(const struct cuckoo_hash_s *cuckoo);


/**
 * @brief remove node from hashing table
 *
 * @param cuckoo to the hashing table pointer.
 * @param node_pp to the node pinter array
 * @param nb to the number of nodes
 * @return Number of removed nodes
 */
extern unsigned cuckoo_del_bulk(struct cuckoo_hash_s *cuckoo,
                                void **user_pp,
                                unsigned nb);

/**
 * @brief Find node from hashing table.
 *
 * @param cuckoo to the hashing table pointer.
 * @param fkey_pp to the node search key array.
 * @param nb to the number of keys.
 * @param node_pp to the node pointer array
 * @param enable_add to the adding key
 * @param enable_chai to the chaining access list
 * @return Number of nodes searched.
 */
extern unsigned cuckoo_find_bulk(struct cuckoo_hash_s *cuckoo,
                                 const void * const *key_pp,
                                 unsigned nb,
                                 void **user_pp,
                                 bool enable_add,
                                 bool enable_chain);


/**
 * @brief Perform hash of key
 *
 * @param cuckoo to the hashing table pointer.
 * @param key_pp to the search pointer array.
 * @param hash_p to the hash array
 * @param nb to the number of keys.
 * @return void
 */
extern void cuckoo_hash_bulk(struct cuckoo_hash_s *cuckoo,
                             const void * const *key_pp,
                             union cuckoo_hash_u *hash_p,
                             unsigned nb);

/**
 * @brief Return the nodes in use in chronological order.
 *
 * @param cuckoo to the hashing table pointer.
 * @param cb_func to the callback function.
 * @param arg to the callback function arguments
 * @return If positive, the number of nodes; if negative, the return value of the callback function.
 */
extern int cuckoo_walk(struct cuckoo_hash_s *cuckoo,
                       int (*cb_func)(struct cuckoo_hash_s *, void *, void *),
                       void *arg);
/**
 * @brief Find node from hashing table.
 *
 * @param cuckoo to the hashing table pointer.
 * @param fkey_p to the saerch key pointer.
 * @return node pointer
 */
static inline void *
cuckoo_find_oneshot(struct cuckoo_hash_s *cuckoo,
                    const void *key_p,
                    bool enable_add,
                    bool enable_chain)
{
        void *user_p = NULL;

        cuckoo_find_bulk(cuckoo, &key_p, 1, &user_p, enable_add, enable_chain);
        return user_p;
}

/**
 * @brief remove node
 *
 * @param cuckoo to the hashing table pointer.
 * @param node to the node pointer.
 * @return void
 */
static inline void
cuckoo_del_oneshot(struct cuckoo_hash_s *cuckoo,
                   void *user)
{
        cuckoo_del_bulk(cuckoo, &user, 1);
}

extern const void *
cuckoo_key(const struct cuckoo_hash_s *cuckoo,
           const void *user);

/************************************************************************************************
 * for debug
 ************************************************************************************************/
extern int cuckoo_flipflop(const struct cuckoo_hash_s *cuckoo,
                           const struct cuckoo_node_s *node);

extern void cuckoo_dump(struct cuckoo_hash_s *cuckoo,
                        FILE *stream,
                        const char *title);

extern void cuckoo_bucket_dump(const struct cuckoo_hash_s *cuckoo,
                               FILE *stream,
                               const char *title,
                               const struct cuckoo_bucket_s *bk);

extern void cuckoo_node_dump(const struct cuckoo_hash_s *cuckoo,
                             FILE *stream,
                             const char *title,
                             const struct cuckoo_node_s *node);

extern void cuckoo_key_dump(const struct cuckoo_hash_s *cuckoo,
                            FILE *stream,
                            const char *title,
                            const void *key);

extern struct cuckoo_bucket_s *cuckoo_current_bucket(const struct cuckoo_hash_s *cuckoo,
                                                     const struct cuckoo_node_s * node);

extern struct cuckoo_bucket_s *cuckoo_another_bucket(const struct cuckoo_hash_s *cuckoo,
                                                     const struct cuckoo_node_s * node);

extern unsigned cuckoo_bk_empty_nb(const struct cuckoo_hash_s *cuckoo,
                                struct cuckoo_bucket_s *bk);

extern int cuckoo_verify(const struct cuckoo_hash_s *cuckoo,
                         const void *user,
                         const void *key);

extern int cuckoo_test(unsigned nb,
                       unsigned ctx_size,
                       bool do_basic,
                       bool do_speed_test,
                       bool do_analyze,
                       bool do_unit,
                       bool do_mem,
                       bool do_hp,
                       bool do_list,
                       unsigned flags);

#endif	/* !_CUCKOOHASH_H_ */
