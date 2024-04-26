/* SPDX-License-Identifier: BSD-2-Clause
 * Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
 */

/*
 * Spec:
 */

#ifndef _CUCKOOHASH_H_
#define _CUCKOOHASH_H_

#include <sys/types.h>
#include <inttypes.h>
#include <errno.h>
#include <stdio.h>
#include <stdbool.h>

#include "index_queue.h"

#ifndef always_inline
# define always_inline  static inline __attribute__ ((__always_inline__))
#endif  /* !always_inline */

#define CUCKOO_CACHELINE_SIZE	64

#ifndef _CUCKOO_CACHE_ALIGNED
# define _CUCKOO_CACHE_ALIGNED	__attribute__((aligned(CUCKOO_CACHELINE_SIZE)))
#endif	/* !_CUCKOO_CACHE_ALIGNED */

#define CUCKOO_BUCKET_ENTRY_SZ	16
#define CUCKOO_NB_ENTRIES_MIN	(CUCKOO_BUCKET_ENTRY_SZ * CUCKOO_BUCKET_ENTRY_SZ * CUCKOO_BUCKET_ENTRY_SZ)
#define CUCKOO_FIND_DEPTH	2
#define CUCKOO_PIPELINE_NB	24


#define CUCKOO_EFFECTIVE_CAPA(nb)	(((nb) / CUCKOO_BUCKET_ENTRY_SZ) * 13)


#define CUCKOO_INVALID_HASH64	UINT64_C(-1)	/* -1 : invalid */
#define CUCKOO_INVALID_HVAL	UINT32_C(-1)
#define CUCKOO_INVALID_IDX	UINT32_C(-1)	/* -1 : invalid */
#define CUCKOO_INVALID_FLAGS	UINT64_C(-1)

/*
 *
 */
enum cuckoo_opt_e {
        CUCKOO_DISABLE_SSE41 = 0,
        CUCKOO_DISABLE_SSE42,
        CUCKOO_DISABLE_AVX2,
        CUCKOO_DISABLE_AVX512,
        CUCKOO_DISABLE_LIST,

        CUCKOO_DISABLE_NB,
};

#define CUCKOO_DISABLE_ALL	(unsigned) -1

#define	CUCKOO_DISABLE_FLAG(opt)	(1 << (opt))
#define CUCKOO_IS_DISABLE(flag, opt)	((flag) & CUCKOO_DISABLE_FLAG((opt)))

/*
 * 8 bytes
 */
union cuckoo_hash_u {
        uint64_t val64;
        uint32_t val32[2];
};

/*
 * 48 + 8 bytes
 */
struct cuckoo_key_s {
        union {
                uint8_t data[48];
                uint32_t d32[12];
                uint64_t d64[6 ];
        } val;
};

/*
 *　128 bytes
 */
struct cuckoo_node_s {
        struct cuckoo_key_s key _CUCKOO_CACHE_ALIGNED;
        IDXQ_ENTRY(cuckoo_node_s) entry;
        union cuckoo_hash_u hash;


        /* flow data */
        uint32_t test_id;
        unsigned data[8];
} _CUCKOO_CACHE_ALIGNED;

struct cuckoo_hash_s;
struct idx_pool_s;
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
typedef union cuckoo_hash_u (*cuckoo_hash_func_t)(const struct cuckoo_key_s *key, uint32_t mask);

/**
 * @brief Function to initialize node
 *
 * @param node pointer
 * @return void
 */
typedef void (*cuckoo_node_initializer_t)(struct cuckoo_node_s *);


/**
 * @brief Generate cuckoo hashing table
 *
 * @param nb to the number of nodes.
 * @param ctx_size to the context number of pipeline.(1 - 8)
 * @param calc_hash to the hash calculater.
 * @param node_init to the node initialize.
 * @param opt_flags to the functional restriction flag.
 * @return cuckoo_hash_s pointer. Use free when destroying.
 */
extern struct cuckoo_hash_s *cuckoo_create(unsigned nb,
                                           unsigned ctx_size,
                                           cuckoo_hash_func_t calc_hash,
                                           cuckoo_node_initializer_t node_init,
                                           unsigned opt_flags);

/**
 * @brief Initialize cuckoo hashing table
 *
 * @param cuckoo to the hashing table pointer.
 * @param nb to the number of nodes.
 * @param ctx_size to the context number of pipeline.(1 - 8)
 * @param calc_hash to the hash calculater.
 * @param node_init to the node initialize.
 * @param opt_flags to the functional restriction flag.
 * @return void
 */
extern void cuckoo_init(struct cuckoo_hash_s *cuckoo,
                        unsigned nb,
                        unsigned ctx_size,
                        cuckoo_hash_func_t calc_hash,
                        cuckoo_node_initializer_t node_init,
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
extern size_t cuckoo_sizeof(unsigned nb);

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
                                struct cuckoo_node_s **node_pp,
                                unsigned nb);

/**
 * @brief Find node from hashing table.
 *
 * @param cuckoo to the hashing table pointer.
 * @param fkey_pp to the node search key array.
 * @param nb to the number of keys.
 * @param node_pp to the node pointer array
 * @return Number of nodes searched.
 */
extern unsigned cuckoo_find_bulk(struct cuckoo_hash_s *cuckoo,
                                 const struct cuckoo_key_s * const *fkey_pp,
                                 unsigned nb,
                                 struct cuckoo_node_s **node_pp);


/**
 * @brief Perform hash of key
 *
 * @param cuckoo to the hashing table pointer.
 * @param key_pp to the search pointer array.
 * @param nb to the number of keys.
 * @return void
 */
extern void cuckoo_hash_bulk(struct cuckoo_hash_s *cuckoo,
                             struct cuckoo_key_s **key_pp,
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
                       int (*cb_func)(struct cuckoo_hash_s *, struct cuckoo_node_s *, void *),
                       void *arg);
/**
 * @brief Find node from hashing table.
 *
 * @param cuckoo to the hashing table pointer.
 * @param fkey_p to the saerch key pointer.
 * @return node pointer
 */
static inline struct cuckoo_node_s *
cuckoo_find_oneshot(struct cuckoo_hash_s *cuckoo,
                    const struct cuckoo_key_s *fkey_p)
{
        struct cuckoo_node_s *node_p = NULL;

        cuckoo_find_bulk(cuckoo, &fkey_p, 1, &node_p);
        return node_p;
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
                   struct cuckoo_node_s *node)
{
        cuckoo_del_bulk(cuckoo, &node, 1);
}

/************************************************************************************************
 * for debug
 ************************************************************************************************/
extern int cuckoo_flipflop(const struct cuckoo_hash_s *cuckoo,
                           const struct cuckoo_node_s *node);

extern void cuckoo_dump(struct cuckoo_hash_s *cuckoo,
                        FILE *stream,
                        const char *title);

extern void cuckoo_idx_pool_dump(const struct idx_pool_s *pool,
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
                            const struct cuckoo_key_s *key,
                            FILE *stream,
                            const char *title);

extern struct cuckoo_bucket_s *cuckoo_current_bucket(const struct cuckoo_hash_s *cuckoo,
                                                     const struct cuckoo_node_s * node);

extern struct cuckoo_bucket_s *cuckoo_another_bucket(const struct cuckoo_hash_s *cuckoo,
                                                     const struct cuckoo_node_s * node);

extern unsigned cuckoo_bk_empty_nb(const struct cuckoo_hash_s *cuckoo,
                                struct cuckoo_bucket_s *bk);

extern int cuckoo_verify(const struct cuckoo_hash_s *cuckoo,
                         const struct cuckoo_node_s *node,
                         const struct cuckoo_key_s *key);

extern int cuckoo_test(unsigned nb,
                       unsigned ctx_size,
                       bool do_basic,
                       bool do_speed_test,
                       bool do_analyze,
                       bool do_unit,
                       bool do_mem,
                       unsigned flags);

#endif	/* !_CUCKOOHASH_H_ */
