/* SPDX-License-Identifier: BSD-2-Clause
 * Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
 */

#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <sched.h>

#include "cuckoohash.h"

#ifndef ARRAYOF
# define ARRAYOF(_a)     (sizeof(_a)/sizeof(_a[0]))
#endif

#ifndef SWAP
# define SWAP(a,b) do { typeof(a) _c = (a); (a) = (b); (b) = _c;} while (0)
#endif

/***************************************************************************************************
 *
 ***************************************************************************************************/

/*
 * 128 bytes
 */
struct cuckoo_bucket_s {
        uint32_t hval[CUCKOO_BUCKET_ENTRY_SZ];		/* hash value */
        uint32_t idx[CUCKOO_BUCKET_ENTRY_SZ];		/* node index */
};

/*
 *
 */
struct idx_pool_s {
        unsigned array_size;
        unsigned nb_used;
        struct cuckoo_node_s *node_array;
        uint32_t *idx_array;
} _CUCKOO_CACHE_ALIGNED;

/*
 *
 */
enum cuckoo_find_state_e {
        CUCKOO_STATE_INVALID = -1,

        CUCKOO_STATE_WAIT_3,
        CUCKOO_STATE_WAIT_2,
        CUCKOO_STATE_WAIT_1,
        CUCKOO_STATE_PREFETCH_KEY,
        CUCKOO_STATE_FETCH_BUCKET,
        CUCKOO_STATE_FETCH_NODE,
        CUCKOO_STATE_REFETCH_NODE,
        CUCKOO_STATE_CMP_KEY,
        CUCKOO_STATE_LISTING,
        CUCKOO_STATE_DONE,

        CUCKOO_STATE_NB,
};

/*
 *
 */
struct cuckoo_find_ctx_s {
        struct {				/* bucket propaties */
                struct cuckoo_bucket_s *ptr;	/* bucket index */
                uint64_t hits;			/* hval match flags */
        } bk[2];				/* Even/Odd */

        union cuckoo_hash_u hash;
        const struct cuckoo_key_s *fkey_p;
        struct cuckoo_node_s **node_pp;

        unsigned idx;				/* request index */
        enum cuckoo_find_state_e state;	/* */
} _CUCKOO_CACHE_ALIGNED;

/*
 *
 */
struct cuckoo_find_engine_s {
        struct cuckoo_find_ctx_s ctx_pool[CUCKOO_PIPELINE_NB];
        struct cuckoo_node_s ** node_pp;
        const struct cuckoo_key_s * const * fkey_pp;
        uint32_t *bk_idx;
        cuckoo_hash_func_t hash_func;

        unsigned ctx_depth;
        unsigned ctx_pool_size;
        unsigned next;
        unsigned req_nb;
        unsigned node_nb;
};

/*
 * Arch handler
 */
typedef uint64_t (*find_idx_in_bucket_t)(const struct cuckoo_hash_s *,
                                         const struct cuckoo_bucket_s *,
                                         uint32_t);
typedef uint64_t (*find_hval_in_bucket_single_t)(const struct cuckoo_hash_s *,
                                                 const struct cuckoo_bucket_s *,
                                                 uint32_t);
typedef void (*find_hval_in_bucket_double_t)(const struct cuckoo_hash_s *,
                                             struct cuckoo_find_ctx_s *);
typedef int (*cmp_key_t)(struct cuckoo_hash_s *,
                         const struct cuckoo_key_s *,
                         const struct cuckoo_key_s *);

typedef int (*debug_fprintf_t)(FILE *stream, const char *format, ...);

IDXQ_HEAD(cuckoo_node_q_s, cuckoo_node_s);

/*
 * cuckoo_hash_s
 * idx pool
 * node array
 * bcuket array
 */
struct cuckoo_hash_s {
        uint32_t bk_mask;		/* bucket index mask */
        unsigned nb;
        unsigned max;
        bool is_debug;
        unsigned ctx_depth;
        unsigned ctx_nb;
        unsigned opt_flags;
        unsigned reserved;

        /* drivers */
        cuckoo_hash_func_t calc_hash;
        find_idx_in_bucket_t find_idx;
        find_hval_in_bucket_single_t find_hval_single;
        find_hval_in_bucket_double_t find_hval_double;
        cmp_key_t cmp_key;
        cuckoo_node_initializer_t node_init;

        /* tables */
        struct idx_pool_s *idx_pool;
        struct cuckoo_bucket_s *buckets;
        struct cuckoo_node_s *nodes;

        uint64_t cnt;
        uint64_t tsc;
        uint64_t fails;

        struct cuckoo_node_q_s used_fifo;

        struct cuckoo_find_engine_s engine _CUCKOO_CACHE_ALIGNED;

        char payload[] _CUCKOO_CACHE_ALIGNED;
};

/******************************************************************************************************
 *
 ******************************************************************************************************/

#if !defined(ENABLE_TRACER)
static int
null_fprintf(FILE *stream __attribute__((unused)),
             const char *format __attribute__((unused)),
             ...)
{
        return 0;
}

static debug_fprintf_t debug_fprintf = null_fprintf;

always_inline void
set_debug_handler(const struct cuckoo_hash_s *cuckoo)
{
        if (cuckoo->is_debug)
                debug_fprintf = fprintf;
}

always_inline void
cls_debug_handler(const struct cuckoo_hash_s *cuckoo)
{
        if (cuckoo->is_debug)
                debug_fprintf = null_fprintf;
}

# define TRACER(fmt,...)        debug_fprintf(stderr, "%s():%d " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
# define TRACER(fmt,...)

//static debug_fprintf_t debug_fprintf = null_fprintf;

always_inline void
set_debug_handler(const struct cuckoo_hash_s *cuckoo __attribute__((unused)))
{
        ;
}

always_inline void
cls_debug_handler(const struct cuckoo_hash_s *cuckoo __attribute__((unused)))
{
        ;
}
#endif

/*******************************************************************************
 * lower
 ******************************************************************************/
/*
 *
 */
always_inline void
prefetch(const void *p,
         const int locality)
{
        __builtin_prefetch(p, 0, locality);    /* non temporal */
}

/*
 * Read Timestamp Counter (x86 only)
 */
always_inline uint64_t
rdtsc(void)
{
        return __builtin_ia32_rdtsc();
}

/*******************************************************************************
 * IDX Pool
 ******************************************************************************/
/*
 *
 */
always_inline size_t
idx_pool_sizeof(unsigned nb)
{
        size_t sz = sizeof(unsigned) * nb;

        return sz;
}

/*
 * Hash Read Method
 */
always_inline uint32_t
hash2val(const union cuckoo_hash_u hash)
{
        return hash.val32[0] ^ hash.val32[1];
}

/*
 * Hash to bucket index (Even/Odd)
 */
always_inline uint32_t
hash2idx(const struct cuckoo_hash_s *cuckoo,
         const union cuckoo_hash_u hash,
         int even_odd)
{
        return (hash.val32[even_odd] & cuckoo->bk_mask);
}

/*
 *
 */
always_inline unsigned
bucket_idx(const struct cuckoo_hash_s *cuckoo,
           const struct cuckoo_bucket_s *bk)
{
        if (!bk)
                return CUCKOO_INVALID_IDX;
        return bk - cuckoo->buckets;
}

/*
 *
 */
always_inline struct cuckoo_bucket_s *
bucket_ptr(const struct cuckoo_hash_s *cuckoo,
           uint32_t idx)
{
        if (idx == CUCKOO_INVALID_IDX)
                return NULL;
        return &cuckoo->buckets[idx];
}

always_inline struct cuckoo_bucket_s *
fetch_bucket(const struct cuckoo_hash_s *cuckoo,
             uint32_t idx)
{
        struct cuckoo_bucket_s *bk = bucket_ptr(cuckoo, idx);
        if (bk) {
                prefetch(bk->hval, 3);
                prefetch(bk->idx, 3);
        }
        return bk;
}

/*
 * current bucket index to another index
 */
always_inline struct cuckoo_bucket_s *
fetch_cuckoo_another_bucket(const struct cuckoo_hash_s *cuckoo,
                            const struct cuckoo_bucket_s *bk,
                            unsigned pos)
{
        uint32_t hval = bk->hval[pos];
        uint32_t idx = ((bucket_idx(cuckoo, bk) ^ hval) & cuckoo->bk_mask);

        return fetch_bucket(cuckoo, idx);
}

/*
 *
 */
always_inline uint32_t
node_idx(const struct cuckoo_hash_s *cuckoo,
         const struct cuckoo_node_s *node)
{
        if (!node)
                return IDXQ_NULL;
        return node - cuckoo->nodes;
}

/*
 *
 */
always_inline struct cuckoo_node_s *
node_ptr(const struct cuckoo_hash_s *cuckoo,
         uint32_t idx)
{
        if (idx == IDXQ_NULL)
                return NULL;
        return &cuckoo->nodes[idx];
}

/*
 *
 */
always_inline struct cuckoo_node_s *
fetch_node(const struct cuckoo_hash_s *cuckoo,
           const struct cuckoo_bucket_s *bk,
           unsigned pos)
{
        struct cuckoo_node_s *n = node_ptr(cuckoo, bk->idx[pos]);
        if (n)
                prefetch(n, 0);
        return n;
}

/*
 *
 */
always_inline struct cuckoo_key_s *
fetch_bk_key(const struct cuckoo_hash_s *cuckoo,
             const struct cuckoo_bucket_s *bk,
             unsigned pos)
{
        struct cuckoo_key_s *key;
        struct cuckoo_node_s *node = node_ptr(cuckoo, bk->idx[pos]);

        if (node) {
                key = &node->key;
                prefetch(key, 1);
        } else {
                key = NULL;
        }
        return key;
}

/*
 *
 */
always_inline void
set_key(struct cuckoo_node_s *node,
        const struct cuckoo_key_s *key,
        union cuckoo_hash_u hash)
{
        if (node) {
                memcpy(&node->key.val, &key->val, sizeof(key->val));
                node->key.hash = hash;
        }
}

/*
 *
 */
always_inline union cuckoo_hash_u
fetch_hash(const struct cuckoo_node_s *node)
{
        if (node)
                return node->key.hash;
        return (union cuckoo_hash_u) CUCKOO_INVALID_HASH64;
}

/*
 *
 */
always_inline void
set_bucket(struct cuckoo_bucket_s *bk,
           unsigned pos,
           uint32_t node_idx,
           uint32_t hval)
{
        bk->hval[pos] = hval;
        bk->idx[pos] = node_idx;
}

/*
 *
 */
always_inline void
move_bucket(struct cuckoo_bucket_s *dst,
            unsigned dpos,
            struct cuckoo_bucket_s *src,
            unsigned spos)
{
        dst->hval[dpos] = src->hval[spos];
        dst->idx[dpos] = src->idx[spos];
        src->hval[spos] = CUCKOO_INVALID_HVAL;
        src->idx[spos] = CUCKOO_INVALID_IDX;
}

/*
 *
 */
always_inline void
idx_pool_prefetch(const struct cuckoo_hash_s *cuckoo)
{
        prefetch(&cuckoo->idx_pool->idx_array[cuckoo->idx_pool->nb_used], 1);
        (void) cuckoo;
}

/*
 *
 */
always_inline void
idx_pool_next_prefetch(const struct cuckoo_hash_s *cuckoo,
                       unsigned nb)
{
        unsigned top = cuckoo->idx_pool->nb_used;
        unsigned tail = top + nb;

        if (tail >= cuckoo->idx_pool->array_size)
                tail = cuckoo->idx_pool->array_size;

        for (unsigned i = top; i < tail; i++) {
                unsigned idx = cuckoo->idx_pool->idx_array[i];

                prefetch(node_ptr(cuckoo, idx), 1);
        }
}

/*
 * prefetch neighbor node in used node queue
 */
always_inline void
prefetch_neighbor(const struct cuckoo_hash_s *cuckoo,
                  const struct cuckoo_node_s *node)
{
        struct cuckoo_node_s *p;

        if ((p = IDXQ_NEXT(&cuckoo->used_fifo, node, entry)) != NULL)
                prefetch(p, 3);

        if ((p = IDXQ_PREV(&cuckoo->used_fifo, node, entry)) != NULL)
                prefetch(p, 3);
}

/*
 *
 */
always_inline void
prefetch_node_in_bucket(const struct cuckoo_hash_s *cuckoo,
                        const struct cuckoo_bucket_s *bk,
                        uint64_t hits)
{
        if (hits) {
                unsigned pos = __builtin_ctzll(hits);

                for (hits >>= pos; hits; pos++, hits >>= 1) {
                        if (hits & 1)
                                fetch_node(cuckoo, bk, pos);
                }
        }
}

#define BUCKET_DRIVER_GENERATE(name)                            		\
static inline uint64_t                                  	        	\
name##_find_idx_in_bucket(const struct cuckoo_hash_s *cuckoo,   		\
                          const struct cuckoo_bucket_s * bk,            	\
                          uint32_t idx)                                 	\
{                                                                       	\
	(void) cuckoo;                                                  	\
        TRACER("bk:%u\n"                                                	\
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          	\
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          	\
               "idx:%08x\n",                                            	\
               bucket_idx(cuckoo, bk),                                  	\
               bk->idx[0], bk->idx[1], bk->idx[2], bk->idx[3],          	\
               bk->idx[4], bk->idx[5], bk->idx[6], bk->idx[7],          	\
               bk->idx[8], bk->idx[9], bk->idx[10], bk->idx[11],        	\
               bk->idx[12], bk->idx[13], bk->idx[14], bk->idx[15],      	\
               idx);                                                    	\
        uint64_t flags = name##_find_32x16(bk->idx, idx);               	\
        TRACER("flags:%04x\n", flags);                                  	\
        return flags;                                                   	\
}                                                                       	\
static inline uint64_t                                                  	\
name##_find_hval_in_bucket_single(const struct cuckoo_hash_s *cuckoo,   	\
                                  const struct cuckoo_bucket_s *bk,     	\
                                  uint32_t hval)                        	\
{                                                                       	\
        (void) cuckoo;                                                  	\
        TRACER("bk:%u\n"                                                	\
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          	\
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          	\
               "hval:%08x\n",                                           	\
               bucket_idx(cuckoo, bk),                                  	\
               bk->hval[0], bk->hval[1], bk->hval[2], bk->hval[3],      	\
               bk->hval[4], bk->hval[5], bk->hval[6], bk->hval[7],      	\
               bk->hval[8], bk->hval[9], bk->hval[10], bk->hval[11],    	\
               bk->hval[12], bk->hval[13], bk->hval[14], bk->hval[15],  	\
               hval);                                                   	\
        uint64_t flags = name##_find_32x16(bk->hval, hval);             	\
        TRACER("flags:%04x\n", flags);                                  	\
        return flags;                                                   	\
}                                                                       	\
static inline void                                                      	\
name##_find_hval_in_bucket_double(const struct cuckoo_hash_s *cuckoo,   	\
                                  struct cuckoo_find_ctx_s *ctx)    	\
{                                                                       	\
        ctx->bk[0].hits =                                               	\
        	name##_find_hval_in_bucket_single(cuckoo,               	\
                                                  ctx->bk[0].ptr,       	\
                                                  hash2val(ctx->hash)); 	\
        ctx->bk[1].hits =                                               	\
                name##_find_hval_in_bucket_single(cuckoo,               	\
                                                  ctx->bk[1].ptr,       	\
                                                  hash2val(ctx->hash));         \
        prefetch_node_in_bucket(cuckoo, ctx->bk[0].ptr, ctx->bk[0].hits);	\
        prefetch_node_in_bucket(cuckoo, ctx->bk[1].ptr, ctx->bk[1].hits);       \
}                                                                               \


/*****************************************************************************
 * default Handler -->
 *****************************************************************************/
always_inline uint64_t
GENERIC_find_32x16(const uint32_t *array,
                   uint32_t val)
{
        uint64_t hits = 0;

        for (unsigned pos = 0; pos < 16; pos++) {
                if (array[pos] == val)
                        hits |= (1 << pos);
        }
        return hits;
}

/*
 *
 */
static inline uint32_t
murmurhash3_32(const uint32_t *blocks,
               unsigned nblocks,
               uint32_t seed)
{
        uint32_t c1 = 0xcc9e2d51;
        uint32_t c2 = 0x1b873593;
        uint32_t r1 = 15;
        uint32_t r2 = 13;
        uint32_t m = 5;
        uint32_t n = 0xe6546b64;
        uint32_t hash = seed;

        for (unsigned i = 0; i < nblocks; i++) {
                uint32_t k = blocks[i];
                k *= c1;
                k = (k << r1) | (k >> (32 - r1));
                k *= c2;

                hash ^= k;
                hash = ((hash << r2) | (hash >> (32 - r2))) * m + n;
        }

        hash ^= (nblocks * 4);
        hash ^= (hash >> 16);
        hash *= 0x85ebca6b;
        hash ^= (hash >> 13);
        hash *= 0xc2b2ae35;
        hash ^= (hash >> 16);

        return hash;
}

/*
 *
 */
static inline union cuckoo_hash_u
GENERIC_calc_hash(const struct cuckoo_key_s *key,
                  uint32_t mask)
{
        union cuckoo_hash_u hash;

        hash.val32[0] = 0;
        hash.val32[1] = 0xdeadbeef;

        for (unsigned i = 0; i < ARRAYOF(key->val.d32); i+=2) {
                hash.val32[0] = murmurhash3_32(&key->val.d32[i], 2, hash.val32[0]);
                hash.val32[1] = murmurhash3_32(&hash.val32[0], 1, hash.val32[1]);
        }

        while (((hash.val32[1] & mask) == (hash.val32[0] & mask)) ||
               ((hash.val32[0] ^ hash.val32[1]) == CUCKOO_INVALID_HVAL)) {
                uint32_t h = __builtin_bswap32(hash.val32[1]);

                h = ~murmurhash3_32(hash.val32, 2, h);
                hash.val32[1] = h ^ hash.val32[0];
        }

        return hash;
}

/*
 *
 */
static inline int
GENERIC_cmp_flow_key(struct cuckoo_hash_s *cuckoo __attribute__((unused)),
                     const struct cuckoo_key_s *dst,
                     const struct cuckoo_key_s *src)
{
        return memcmp(&dst->val, &src->val, sizeof(dst->val));
}

BUCKET_DRIVER_GENERATE(GENERIC);

/*****************************************************************************
 * <-- default Handler
 *****************************************************************************/

#if defined(__x86_64__)
#include <x86intrin.h>
#include <cpuid.h>

/*****************************************************************************
 * SSE4.1 depened code -->
 *****************************************************************************/
#if defined(__SSE4_1__)

/*
 *
 */
always_inline uint64_t
SSE41_cmp_flag(const __m128i *hash,
               const __m128i key)
{
        uint64_t flags = 0;

        for (unsigned i = 0; i < 4; i++) {
                __m128i cmp_result = _mm_cmpeq_epi32(key, hash[i]);
                flags |= _mm_movemask_ps(_mm_castsi128_ps(cmp_result)) << (i * 4);
        }
        return flags;
}

/*
 *
 */
always_inline uint64_t
SSE41_find_32x16(const uint32_t *array,
                 uint32_t val)
{
        __m128i target[4];
        __m128i key = _mm_set1_epi32(val);

        for (unsigned i = 0; i < ARRAYOF(target); i++)
                target[i] = _mm_load_si128((__m128i *) (volatile void *) &array[i * 4]);
        return SSE41_cmp_flag(target, key);
}

/*
 *
 */
static inline int
SSE41_cmp_flow_key(struct cuckoo_hash_s *cuckoo __attribute__((unused)),
                   const struct cuckoo_key_s *a,
                   const struct cuckoo_key_s *b)
{
        const __m128i * ptr_a = (const __m128i *) a;
        const __m128i * ptr_b = (const __m128i *) b;
        unsigned mask = 0xFFFF;

        TRACER("a:%p b:%p\n", a, b);

        for (unsigned i = 0; i < 3; i++) {
                __m128i chunk1_a = _mm_loadu_si128(&ptr_a[i]);
                __m128i chunk1_b = _mm_loadu_si128(&ptr_b[i]);
                __m128i result1 = _mm_cmpeq_epi8(chunk1_a, chunk1_b);

                mask &= _mm_movemask_epi8(result1);
        }

        TRACER("mask:%08x\n", mask);
        return (mask != 0xFFFF);
}

BUCKET_DRIVER_GENERATE(SSE41);

#endif
/*****************************************************************************
 * <-- SSE4.1 depened code
 *****************************************************************************/

/*****************************************************************************
 * SSE4.2 depened code -->
 *****************************************************************************/
#if defined(__SSE4_2__)
/*
 *
 */
static inline union cuckoo_hash_u
SSE42_calc_hash(const struct cuckoo_key_s *key,
                uint32_t mask)
{
        union cuckoo_hash_u hash;

        hash.val32[0] = 0;
        hash.val32[1] = 0xdeadbeef;

        for (unsigned i = 0; i < ARRAYOF(key->val.d64); i++) {
                hash.val32[0] = _mm_crc32_u64(hash.val32[0], key->val.d64[i]);
                hash.val32[1] = __builtin_bswap32(hash.val32[0]) ^ hash.val32[1];
        }

        while (((hash.val32[1] & mask) == (hash.val32[0] & mask)) ||
               ((hash.val32[0] ^ hash.val32[1]) == CUCKOO_INVALID_HVAL)) {
                uint32_t h = __builtin_bswap32(hash.val32[1]);

                h = ~_mm_crc32_u64(h, hash.val64);
                hash.val32[1] = h ^ hash.val32[0];
        }
        return hash;
}
#endif
/*****************************************************************************
 * <--- SSE4.2 depened code
 *****************************************************************************/

/*****************************************************************************
 * AVX2 depened code -->
 *****************************************************************************/
#if defined(__AVX2__)
/*
 *
 */
always_inline uint64_t
AVX2_cmp_flag(const __m256i hash_lo,
              const __m256i hash_hi,
              const __m256i key)
{
        uint64_t mask_lo = _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(key, hash_lo)));
        uint64_t mask_hi = _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(key, hash_hi)));
        return (mask_hi << 8) | mask_lo;
}

/*
 *
 */
always_inline uint64_t
AVX2_find_32x16(const uint32_t *array,
                uint32_t val)
{
        return AVX2_cmp_flag(_mm256_load_si256((__m256i *) (volatile void *) &array[0]),
                             _mm256_load_si256((__m256i *) (volatile void *) &array[8]),
                             _mm256_set1_epi32(val));
}

/*
 *
 */
static inline int
AVX2_cmp_flow_key(struct cuckoo_hash_s *cuckoo __attribute__((unused)),
                  const struct cuckoo_key_s *a,
                  const struct cuckoo_key_s *b)
{
        const __m256i * ptr_a = (const __m256i *) a;
        const __m256i * ptr_b = (const __m256i *) b;

        TRACER("a:%p b:%p\n", a, b);

        __m256i chunk1_a = _mm256_loadu_si256(ptr_a);
        __m256i chunk1_b = _mm256_loadu_si256(ptr_b);
        __m256i result1 = _mm256_cmpeq_epi8(chunk1_a, chunk1_b);
        int mask1 = _mm256_movemask_epi8(result1);

        const __m128i * ptr_a128 = (const __m128i *) (ptr_a + 1);
        const __m128i * ptr_b128 = (const __m128i *) (ptr_b + 1);
        __m128i chunk2_a = _mm_loadu_si128(ptr_a128);
        __m128i chunk2_b = _mm_loadu_si128(ptr_b128);
        __m128i result2 = _mm_cmpeq_epi8(chunk2_a, chunk2_b);
        int mask2 = _mm_movemask_epi8(result2);

        TRACER("mask1:%08x mask2:%08x\n", mask1, mask2);
        return !((mask1 == -1) && (mask2 == 0xFFFF));
}

BUCKET_DRIVER_GENERATE(AVX2);

#endif /* __AVX2__ */

/*****************************************************************************
 * <--- AVX2 depened code
 *****************************************************************************/

/*****************************************************************************
 * AVX512 depened code -->
 *****************************************************************************/
#if defined(__AVX512F__)
/*
 *
 */
always_inline uint64_t
AVX512_cmp_flag(__m512i hash,
                __m512i key)
{
        return _mm512_cmpeq_epi32_mask(key, hash);
}

/*
 *
 */
always_inline uint64_t
AVX512_find_32x16(const uint32_t *array,
                  uint32_t val)
{
        __m512i target = _mm512_load_si512((__m512i *) (volatile void *) array);
        __m512i key = _mm512_set1_epi32(val);

        return AVX512_cmp_flag(target, key);
}

BUCKET_DRIVER_GENERATE(AVX512);

#endif /* __AVX512F__ */
/*****************************************************************************
 * <--- AVX512 depened code
 *****************************************************************************/

/*
 * check cpuid AVX2,BMI,SSE4_2(crc32c)
 */
static void
x86_handler_init (struct cuckoo_hash_s *cuckoo,
                  unsigned flags)
{
        uint32_t eax = 0, ebx, ecx, edx;

        // Get the highest function parameter.
        __get_cpuid(0, &eax, &ebx, &ecx, &edx);

        // Check if the function parameter for extended features is available.
        if (eax >= 7) {
                __cpuid_count(1, 0, eax, ebx, ecx, edx);

#if defined(__SSE4_1__)
                if (!CUCKOO_IS_DISABLE(flags, CUCKOO_DISABLE_SSE41) && (ecx & bit_SSE4_1)) {
                        TRACER("use SSE4.1 ready\n");

                        cuckoo->find_idx         = SSE41_find_idx_in_bucket;
                        cuckoo->find_hval_single = SSE41_find_hval_in_bucket_single;
                        cuckoo->find_hval_double = SSE41_find_hval_in_bucket_double;
                        cuckoo->cmp_key          = SSE41_cmp_flow_key;
                }
#endif

#if defined(__SSE4_2__)
                if (!CUCKOO_IS_DISABLE(flags, CUCKOO_DISABLE_SSE42) && (ecx & bit_SSE4_2)) {
                        TRACER("use SSE4.2 ready\n");

                        cuckoo->calc_hash = SSE42_calc_hash;
                }
#endif
                __cpuid_count(7, 0, eax, ebx, ecx, edx);

#if defined(__AVX2__)
                if (!CUCKOO_IS_DISABLE(flags, CUCKOO_DISABLE_AVX2) && (ebx & bit_AVX2)) {
                        TRACER("use AVX2 ready\n");

                        cuckoo->find_idx         = AVX2_find_idx_in_bucket;
                        cuckoo->find_hval_single = AVX2_find_hval_in_bucket_single;
                        cuckoo->find_hval_double = AVX2_find_hval_in_bucket_double;
                        cuckoo->cmp_key          = AVX2_cmp_flow_key;
                }
#endif

#if defined(__AVX512F__)
                if (!CUCKOO_IS_DISABLE(flags, CUCKOO_DISABLE_AVX512) && (ebx & bit_AVX512F)) {
                        TRACER("use AVX512F ready\n");

                        cuckoo->find_idx         = AVX512_find_idx_in_bucket;
                        cuckoo->find_hval_single = AVX512_find_hval_in_bucket_single;
                        cuckoo->find_hval_double = AVX512_find_hval_in_bucket_double;
                }
#endif
        }
}
/* __x86_64__ */
#elif defined(__ARM_NEON__)
/*
 * TBD, not yet
 */
#include <arm_neon.h>

/*
 *
 */
always_inline uint64_t
NEON_cmp_flag(uint32x4_t hash_lo,
              uint32x4_t hash_hi,
              uint32x4_t key)
{
        uint32x4_t result_lo = vceqq_u32(key, hash_lo);
        uint32x4_t result_hi = vceqq_u32(key, hash_hi);
        uint16x8_t combined = vcombine_u16(vmovn_u32(result_lo), vmovn_u32(result_hi));
        return vget_lane_u64(vreinterpret_u64_u16(combined), 0);
}

/*
 *
 */
always_inline uint64_t
NEON_find_32x16(const uint32_t *array,
                uint32_t val)
{
        // NEON specific code
        uint32x4_t key = vdupq_n_u32(val);
        uint32x4_t hash_lo0 = vld1q_u32(&array[0]);
        uint32x4_t hash_lo1 = vld1q_u32(&array[4]);
        uint32x4_t hash_hi0 = vld1q_u32(&array[8]);
        uint32x4_t hash_hi1 = vld1q_u32(&array[12]);
        uint64_t mask_lo = neon_cmp_flag(hash_lo0, hash_lo1, key);
        uint64_t mask_hi = neon_cmp_flag(hash_hi0, hash_hi1, key);
        return (mask_hi << 16) | mask_lo;
}

BUCKET_DRIVER_GENERATE(NEON);

/*
 *
 */
static void
arm_handler_init(struct cuckoo_hash_s *cuckoo,
                 unsigned flags __attribute__((unused)))
{
        cuckoo->find_idx         = NEON_find_idx_in_bucket;
        cuckoo->find_hval_single = NEON_find_hval_in_bucket_single;
        cuckoo->find_hval_double = NEON_find_hval_in_bucket_double;
        cuckoo->cmp_key          = NEON_cmp_flow_key;
}
#endif /* __ARM_NEON__ */

/*******************************************************************************
 * IDX Pool
 ******************************************************************************/
/*
 *
 */
always_inline void
idx_pool_init(struct idx_pool_s *idx_pool,
              unsigned nb,
              struct cuckoo_node_s *node_array __attribute__((unused)),
              void *idx_array)
{
        TRACER("idx_pool:%p nb:%u node_array:%p idx_array:%p\n",
               idx_pool, nb, node_array, idx_array);

        idx_pool->array_size = nb;
        //        idx_pool->node_array = node_array;
        idx_pool->idx_array = idx_array;
        idx_pool->nb_used = 0;

        for (uint32_t idx = 0; idx < nb; idx++)
                idx_pool->idx_array[idx] = idx;
}

/*
 *
 */
always_inline uint32_t
idx_pool_alloc(struct cuckoo_hash_s *cuckoo)
{
        uint32_t idx = CUCKOO_INVALID_IDX;

        if (cuckoo->idx_pool->array_size > cuckoo->idx_pool->nb_used) {
                idx = cuckoo->idx_pool->idx_array[cuckoo->idx_pool->nb_used++];
                idx_pool_next_prefetch(cuckoo, 2);
        }

        TRACER("node:%u\n", idx);
        return idx;
}

/*
 *
 */
always_inline void
idx_pool_free(struct cuckoo_hash_s *cuckoo,
              uint32_t idx)
{
        if (idx != CUCKOO_INVALID_IDX) {
                cuckoo->idx_pool->idx_array[--(cuckoo->idx_pool->nb_used)] = idx;
        }
}

/*
 *
 */
always_inline struct cuckoo_bucket_s *
fetch_cuckoo_current_bucket(const struct cuckoo_hash_s *cuckoo,
                            const struct cuckoo_node_s *node,
                            unsigned *pos_p)
{
        union cuckoo_hash_u hash = fetch_hash(node);
        uint32_t idx = node_idx(cuckoo, node);
        struct cuckoo_bucket_s *bk = NULL;

        for (int eo = 0; eo < 2; eo++) {
                bk = bucket_ptr(cuckoo, hash2idx(cuckoo, hash, eo));

                uint64_t hits = cuckoo->find_idx(cuckoo, bk, idx);
                if (hits) {
                        *pos_p = __builtin_ctzll(hits);
                        goto end;
                }
                bk = NULL;
        }

 end:
        TRACER("bucket:%u pos:%u node:%u\n",
               bucket_idx(cuckoo, bk), *pos_p, idx);
        return bk;
}

/*******************************************************************************
 * Node manager
 ******************************************************************************/
/*
 *
 */
always_inline struct cuckoo_node_s *
fetch_old_node(const struct cuckoo_hash_s *cuckoo)
{
        return IDXQ_FIRST(&cuckoo->used_fifo);
}

/*
 * Number of Empty Slot in Bucket
 */
unsigned
cuckoo_bk_empty_nb(const struct cuckoo_hash_s *cuckoo,
                struct cuckoo_bucket_s *bk)
{
        uint64_t mask = cuckoo->find_hval_single(cuckoo, bk, CUCKOO_INVALID_HVAL);

        return __builtin_popcountll(mask);
}

/*
 *
 */
always_inline void
refetch_bucket(struct cuckoo_find_engine_s *engine,
               const struct cuckoo_bucket_s *bk)
{
        for (unsigned i = 0; i < engine->ctx_pool_size; i++) {
                if (engine->ctx_pool[i].state != CUCKOO_STATE_CMP_KEY)
                        continue;

                if (engine->ctx_pool[i].bk[0].ptr == bk ||
                    engine->ctx_pool[i].bk[1].ptr == bk)
                        engine->ctx_pool[i].state = CUCKOO_STATE_REFETCH_NODE;
        }
}

/**
 * @brief Set all bits below MSB
 *
 * @param v: input integer
 * @return integer
 */
always_inline unsigned
combine_ms1b (unsigned v)
{
        v |= v >> 1;
        v |= v >> 2;
        v |= v >> 4;
        v |= v >> 8;
        v |= v >> 16;

        return v;
}

/**
 * @brief Returns the nearest power of 2 times greater than
 *
 * @param input integer
 * @return integer
 */
always_inline unsigned
align_pow2 (unsigned v)
{
        v--;
        v = combine_ms1b(v);
        return v + 1;
}

/*
 *
 */
always_inline unsigned
nb_nodes (unsigned nb_entries)
{
        nb_entries = nb_entries * 16 / 15;
        if (nb_entries < CUCKOO_NB_ENTRIES_MIN)
                nb_entries = CUCKOO_NB_ENTRIES_MIN;
        nb_entries = align_pow2(nb_entries);

        TRACER("nb nodes:%u\n", nb_entries);
        return nb_entries;
}

/*
 * max buckets + 1
 */
always_inline unsigned
nb_buckets (unsigned nb_entries)
{
        unsigned nb_buckets = nb_entries / CUCKOO_BUCKET_ENTRY_SZ;

        TRACER("nb buckets:%u\n", nb_buckets);
        return nb_buckets;
}

/***************************************************************************************************
 * Context Engine
 **************************************************************************************************/
/*
 *
 */
always_inline int
flipflop_bucket(const struct cuckoo_hash_s *cuckoo,
                struct cuckoo_find_engine_s *engine,
                struct cuckoo_bucket_s *src_bk,
                unsigned src_pos)
{
        struct cuckoo_bucket_s *dst_bk = fetch_cuckoo_another_bucket(cuckoo, src_bk, src_pos);
        unsigned dst_pos = -1;
        int ret = -1;

        uint64_t empty = cuckoo->find_hval_single(cuckoo, dst_bk, CUCKOO_INVALID_HVAL);
        if (empty) {
                dst_pos = __builtin_ctzll(empty);

                move_bucket(dst_bk, dst_pos, src_bk, src_pos);

                if (engine) {
                        refetch_bucket(engine, dst_bk);
                        refetch_bucket(engine, src_bk);
                }

                ret = 0;
        }

        TRACER("src bk:%u pos:%u  dst bk:%u pos:%u ret:%d\n",
               bucket_idx(cuckoo, src_bk), src_pos,
               bucket_idx(cuckoo, dst_bk), dst_pos,
               ret);
        return ret;
}

/*
 * kick out egg
 */
static int
kickout_node(const struct cuckoo_hash_s *cuckoo,
             struct cuckoo_find_engine_s *engine,
             struct cuckoo_bucket_s *bk,
             int cnt)
{
        int pos = -1;

        TRACER("bk:%u cnt:%d\n", bucket_idx(cuckoo, bk), cnt);
        if (cnt--) {
                for (unsigned i = 0; i < CUCKOO_BUCKET_ENTRY_SZ; i++) {
                        if (!flipflop_bucket(cuckoo, engine, bk, i)) {
                                pos = i;
                                goto end;
                        }
                }

                for (unsigned i = 0; i < CUCKOO_BUCKET_ENTRY_SZ; i++) {
                        struct cuckoo_bucket_s *ano_bk;

                        ano_bk = fetch_cuckoo_another_bucket(cuckoo, bk, i);
                        if (kickout_node(cuckoo, engine, ano_bk, cnt) < 0)
                                continue;

                        if (!flipflop_bucket(cuckoo, engine, bk, i)) {
                                pos = i;
                                goto end;
                        }
                }
        }
 end:
        return pos;
}

/*
 *
 */
always_inline struct cuckoo_node_s *
find_node_in_bucket(const struct cuckoo_hash_s *cuckoo,
                    const struct cuckoo_bucket_s *bk,
                    uint64_t hits,
                    const struct cuckoo_key_s *fkey,
                    unsigned *pos_p)
{
        struct cuckoo_node_s *node = NULL;
        unsigned pos = -1;

        TRACER("bk:%u fkey:%p hits:%"PRIx64"\n", bucket_idx(cuckoo, bk), fkey, hits);

        if (hits) {
                pos = __builtin_ctzll(hits);
                for (hits >>= pos; hits; pos++, hits >>= 1) {
                        if (hits & 1) {
                                node = fetch_node(cuckoo, bk, pos);
                                if (!memcmp(&node->key.val, &fkey->val, sizeof(node->key.val))) {
                                        *pos_p = pos;
                                        break;
                                }
                                node = NULL;
                                TRACER("mismatched.\n");
                        }
                }
        }

        TRACER("node:%u pos:%u\n", node_idx(cuckoo, node), pos);
        return node;
}

/*
 *
 */
static struct cuckoo_node_s *
insert_node(struct cuckoo_hash_s *cuckoo,
            struct cuckoo_find_engine_s *engine,
            struct cuckoo_find_ctx_s *ctx)
{
        struct cuckoo_bucket_s *bk;
        int pos;
        uint32_t node_idx = CUCKOO_INVALID_IDX;

        TRACER("bk[0]:%u bk[1]:%u hval:%08x\n",
               bucket_idx(cuckoo, ctx->bk[0].ptr), bucket_idx(cuckoo, ctx->bk[1].ptr),
               hash2val(ctx->hash));

        uint64_t empt[2];

#if 0
        empt[0] = cuckoo->find_hval_single(cuckoo, ctx->bk[0].ptr, CUCKOO_INVALID_HVAL);
        empt[1] = cuckoo->find_hval_single(cuckoo, ctx->bk[1].ptr, CUCKOO_INVALID_HVAL);
        if (empt[0] || empt[1]) {
                /* which use bk[0] or bk[1] */

                unsigned cnt[2];

                cnt[0] = __builtin_popcountll(empt[0]);
                cnt[1] = __builtin_popcountll(empt[1]);

                TRACER("Count bk[0]:%u bk[1]:%u\n", cnt[0], cnt[1]);

                if (cnt[0] < cnt[1]) {
                        bk = ctx->bk[1].ptr;
                        pos = __builtin_ctzll(empt[1]);
                } else {
                        bk = ctx->bk[0].ptr;
                        pos = __builtin_ctzll(empt[0]);
                }
        }
#else
        empt[0] = cuckoo->find_hval_single(cuckoo, ctx->bk[0].ptr, CUCKOO_INVALID_HVAL);
        if (!empt[0])
                empt[1] = cuckoo->find_hval_single(cuckoo, ctx->bk[1].ptr, CUCKOO_INVALID_HVAL);

        if (empt[0]) {
                bk = ctx->bk[0].ptr;
                pos = __builtin_ctzll(empt[0]);
        } else if (empt[1]) {
                bk = ctx->bk[1].ptr;
                pos = __builtin_ctzll(empt[1]);
        }
#endif
        else {
                /* No Vacancy */
                pos = kickout_node(cuckoo, engine, ctx->bk[0].ptr, CUCKOO_MAX_DEPTH);
                if (pos < 0) {
                        pos = kickout_node(cuckoo, engine, ctx->bk[1].ptr, CUCKOO_MAX_DEPTH);
                        if (pos < 0) {
                                /* error */
                                TRACER("failed to insert node\n");
                                goto end;
                        }
                        bk = ctx->bk[1].ptr;
                } else {
                        bk = ctx->bk[0].ptr;
                }
        }

        node_idx = idx_pool_alloc(cuckoo);
        if (node_idx != CUCKOO_INVALID_IDX) {
                set_bucket(bk, pos, node_idx, hash2val(ctx->hash));
                set_key(node_ptr(cuckoo, node_idx), ctx->fkey_p, ctx->hash);

                cuckoo->node_init(node_ptr(cuckoo, node_idx));

                refetch_bucket(engine, bk);

                TRACER("node:%u bk:%u pos:%d\n", node_idx, bucket_idx(cuckoo, bk), pos);
        } else {
                TRACER("failed to allcate node\n");
        }
 end:
        return node_ptr(cuckoo, node_idx);
}

/*
 *
 */
static inline union cuckoo_hash_u
read_hash(const struct cuckoo_key_s *key,
          uint32_t mask __attribute__((unused)))
{
        return key->hash;
}

/*
 *
 */
always_inline void
init_find_engine(struct cuckoo_find_engine_s *engine,
                 unsigned nb,
                 struct cuckoo_node_s **node_pp,
                 const struct cuckoo_key_s * const *fkey_pp,
                 unsigned ctx_depth,
                 unsigned ctx_nb)
{
        engine->node_pp = node_pp;
        engine->fkey_pp = fkey_pp;
        engine->next = 0;
        engine->req_nb = nb;
        engine->node_nb = 0;

        engine->ctx_depth = ctx_depth;
        engine->ctx_pool_size = ctx_depth * ctx_nb;

        for (unsigned i = 0; i < engine->ctx_pool_size; i++) {
                engine->ctx_pool[i].idx = CUCKOO_INVALID_IDX;

                switch (i % ctx_depth) {
                case 0:
                        engine->ctx_pool[i].state = CUCKOO_STATE_PREFETCH_KEY;
                        break;
                case 1:
                        engine->ctx_pool[i].state = CUCKOO_STATE_WAIT_1;
                        break;
                case 2:
                        engine->ctx_pool[i].state = CUCKOO_STATE_WAIT_2;
                        break;
                case 3:
                        engine->ctx_pool[i].state = CUCKOO_STATE_WAIT_3;
                        break;
                }
        }
}

/*
 *
 */
always_inline unsigned
do_find_ctx(struct cuckoo_hash_s *cuckoo,
            struct cuckoo_find_engine_s *engine,
            const unsigned nb,
            struct cuckoo_find_ctx_s *ctx)
{
        unsigned done = 0;

        TRACER("Start--> nb:%u next:%u ctx:%ld state:%d idx:%u\n",
               nb, engine->next,
               ctx - engine->ctx_pool, ctx->state, ctx->idx);

        switch (ctx->state) {
        case CUCKOO_STATE_WAIT_3:
        case CUCKOO_STATE_WAIT_2:
        case CUCKOO_STATE_WAIT_1:
                if (engine->next < nb)
                        ctx->state += 1;
                else
                        ctx->state = CUCKOO_STATE_DONE;
                break;

        case CUCKOO_STATE_PREFETCH_KEY:
                if (engine->next < nb) {
                        ctx->idx     = engine->next++;
                        ctx->fkey_p  = engine->fkey_pp[ctx->idx];
                        ctx->node_pp = &engine->node_pp[ctx->idx];

                        prefetch(ctx->fkey_p, 0);

                        ctx->state = CUCKOO_STATE_FETCH_BUCKET;
                } else {
                        ctx->state = CUCKOO_STATE_DONE;
                }
                break;

        case CUCKOO_STATE_FETCH_BUCKET:
                /* calk hash and fetch bucket */
                ctx->hash = engine->hash_func(ctx->fkey_p, cuckoo->bk_mask);

                ctx->bk[0].ptr  = fetch_bucket(cuckoo, hash2idx(cuckoo, ctx->hash, 0));
                ctx->bk[0].hits = CUCKOO_INVALID_FLAGS;

                ctx->bk[1].ptr  = fetch_bucket(cuckoo, hash2idx(cuckoo, ctx->hash, 1));
                ctx->bk[1].hits = CUCKOO_INVALID_FLAGS;

                ctx->state = CUCKOO_STATE_FETCH_NODE;
                break;

        case CUCKOO_STATE_FETCH_NODE:
                /* find hash value in bucket */
                cuckoo->find_hval_double(cuckoo, ctx);
                ctx->state = CUCKOO_STATE_CMP_KEY;
                break;

        case CUCKOO_STATE_REFETCH_NODE:
                cuckoo->find_hval_double(cuckoo, ctx);
                /* fall through */

        case CUCKOO_STATE_CMP_KEY:
                {
                        struct cuckoo_node_s *node;
                        unsigned pos;

                        node = find_node_in_bucket(cuckoo, ctx->bk[0].ptr, ctx->bk[0].hits,
                                                   ctx->fkey_p, &pos);
                        if (!node)
                                node = find_node_in_bucket(cuckoo, ctx->bk[1].ptr, ctx->bk[1].hits,
                                                           ctx->fkey_p, &pos);
                        if (!node) {
                                node = insert_node(cuckoo, engine, ctx);
                                if (node)
                                        IDXQ_INSERT_HEAD(&cuckoo->used_fifo, node, entry);
                        }

                        *ctx->node_pp = node;

                        if (CUCKOO_IS_DISABLE(cuckoo->opt_flags, CUCKOO_DISABLE_LIST)) {
                                if (node) {
                                        engine->node_nb += 1;
                                } else {
                                        cuckoo->fails += 1;
                                }

                                if (engine->next < nb) {
                                        ctx->idx     = engine->next++;
                                        ctx->fkey_p  = engine->fkey_pp[ctx->idx];
                                        ctx->node_pp = &engine->node_pp[ctx->idx];

                                        prefetch(ctx->fkey_p, 1);

                                        ctx->state = CUCKOO_STATE_FETCH_BUCKET;
                                } else {
                                        ctx->idx = CUCKOO_INVALID_IDX;
                                        ctx->state = CUCKOO_STATE_DONE;
                                }
                                done = 1;
                        } else {
                                if (node)
                                        prefetch_neighbor(cuckoo, node);
                                ctx->state = CUCKOO_STATE_LISTING;
                        }
                }
                break;

        case CUCKOO_STATE_LISTING:
                if (*ctx->node_pp) {
                        struct cuckoo_node_s *node = *ctx->node_pp;

                        IDXQ_REMOVE(&cuckoo->used_fifo, node, entry);
                        IDXQ_INSERT_HEAD(&cuckoo->used_fifo, node, entry);

                        engine->node_nb += 1;
                } else {
                        cuckoo->fails += 1;
                }

                if (engine->next < nb) {
                        ctx->idx     = engine->next++;
                        ctx->fkey_p  = engine->fkey_pp[ctx->idx];
                        ctx->node_pp = &engine->node_pp[ctx->idx];

                        prefetch(ctx->fkey_p, 0);

                        ctx->state = CUCKOO_STATE_FETCH_BUCKET;
                } else {
                        ctx->idx = CUCKOO_INVALID_IDX;
                        ctx->state = CUCKOO_STATE_DONE;
                }
                done = 1;
                break;

        case CUCKOO_STATE_DONE:
        default:
                break;
        }

        TRACER("<--  End nb:%u next:%u ctx:%ld state:%d idx:%u done:%u\n",
               nb, engine->next,
               ctx - engine->ctx_pool, ctx->state, ctx->idx,
               done);

        return done;
}

/*
 *
 */
always_inline unsigned
find_engine(struct cuckoo_hash_s *cuckoo,
            struct cuckoo_node_s **node_pp,
            const struct cuckoo_key_s * const *fkey_pp,
            unsigned nb,
            int with_hash)
{
        struct cuckoo_find_engine_s *engine = &cuckoo->engine;
        unsigned cnt = 0;

        set_debug_handler(cuckoo);

        uint64_t tsc = rdtsc();
        idx_pool_next_prefetch(cuckoo, 2);

        init_find_engine(engine, nb, node_pp, fkey_pp,
                         cuckoo->ctx_depth, cuckoo->ctx_nb);

        if (with_hash)
                engine->hash_func = read_hash;
        else
                engine->hash_func = cuckoo->calc_hash;

        while (nb > cnt) {
                for (unsigned i = 0; (nb > cnt) && (i < engine->ctx_pool_size); i++) {
                        cnt += do_find_ctx(cuckoo, engine, nb, &engine->ctx_pool[i]);
                }
        }

        if (cnt) {
                cuckoo->tsc += (rdtsc() - tsc);
                cuckoo->cnt += cnt;
        }

        cls_debug_handler(cuckoo);

        return engine->node_nb;
}

/*
 *
 */
static void
null_node_init(struct cuckoo_node_s *node __attribute__((unused)))
{
        /* nothing to do */
}

/***************************************************************************************************
 * API
 ***************************************************************************************************/
/*
 *
 */
union cuckoo_hash_u
cuckoo_calc_hash(const struct cuckoo_hash_s *cuckoo,
                 const struct cuckoo_key_s *key)
{
        return cuckoo->calc_hash(key, cuckoo->bk_mask);
}

/*
 *
 */
unsigned
cuckoo_find_bulk(struct cuckoo_hash_s *cuckoo,
                 const struct cuckoo_key_s * const *fkey_pp,
                 unsigned nb,
                 struct cuckoo_node_s **node_pp,
                 int with_hash)
{
        return find_engine(cuckoo, node_pp, fkey_pp, nb, with_hash);
}

/*
 *
 */
size_t
cuckoo_sizeof(unsigned nb)
{
        size_t sz = sizeof(struct cuckoo_hash_s) + sizeof(struct idx_pool_s);

        nb = nb_nodes(nb);
        sz += sizeof(struct cuckoo_bucket_s) * nb_buckets(nb);

        sz += sizeof(struct cuckoo_node_s) * nb;
        sz += idx_pool_sizeof(nb);

        TRACER("nb:%u sz:%zu\n", nb, sz);
        return sz;
}

/*
 *
 */
void
cuckoo_init(struct cuckoo_hash_s *cuckoo,
            unsigned nb,
            unsigned ctx_nb,
            cuckoo_hash_func_t func,
            cuckoo_node_initializer_t node_init,
            unsigned flags)
{
        TRACER("cuckoo:%p nb:%u ctx:%u\n", cuckoo, nb, ctx_size);

        if (!ctx_nb)
                ctx_nb = 1;

        unsigned node_nb = nb_nodes(nb);
        unsigned bucket_nb = nb_buckets(node_nb);

        TRACER("re-size node:%u bucket:%u\n", node_nb, bucket_nb);

        cuckoo->max = (node_nb / 16) * 15;
        cuckoo->bk_mask = (uint32_t) bucket_nb - 1;
        cuckoo->nb = node_nb;
        cuckoo->cnt = 0;

        cuckoo->tsc = 0;
        cuckoo->fails = 0;
        cuckoo->is_debug = false;
        cuckoo->opt_flags = flags;

        if (CUCKOO_IS_DISABLE(flags, CUCKOO_DISABLE_LIST))
                cuckoo->ctx_depth = 3;
        else
                cuckoo->ctx_depth = 4;

        if ((ctx_nb * cuckoo->ctx_depth) > ARRAYOF(cuckoo->engine.ctx_pool))
                cuckoo->ctx_nb = ARRAYOF(cuckoo->engine.ctx_pool) / cuckoo->ctx_depth;
        else
                cuckoo->ctx_nb = ctx_nb;

        cuckoo->find_idx         = GENERIC_find_idx_in_bucket;
        cuckoo->find_hval_single = GENERIC_find_hval_in_bucket_single;
        cuckoo->find_hval_double = GENERIC_find_hval_in_bucket_double;
        cuckoo->cmp_key          = GENERIC_cmp_flow_key;
        cuckoo->calc_hash        = GENERIC_calc_hash;

#if defined(__x86_64__)
        x86_handler_init(cuckoo, flags);
#elif defined(__ARM_NEON__)
        arm_handler_init(cuckoo, 0);
#endif

        if (func)
                cuckoo->calc_hash = func;

        if (node_init)
                cuckoo->node_init = node_init;
        else
                cuckoo->node_init = null_node_init;

        size_t sz = 0;

        cuckoo->idx_pool = (struct idx_pool_s *) &cuckoo->payload[sz];
        sz += sizeof(*(cuckoo->idx_pool));

        cuckoo->buckets = (struct cuckoo_bucket_s *) &cuckoo->payload[sz];
        memset(cuckoo->buckets, -1, sizeof(struct cuckoo_bucket_s) * bucket_nb);
        sz += sizeof(struct cuckoo_bucket_s) * bucket_nb;

        cuckoo->nodes = (struct cuckoo_node_s *) &cuckoo->payload[sz];
        memset(cuckoo->nodes, -1, sizeof(struct cuckoo_node_s) * node_nb);
        sz += sizeof(struct cuckoo_node_s) * node_nb;

        IDXQ_INIT(&cuckoo->used_fifo, cuckoo->nodes);

        idx_pool_init(cuckoo->idx_pool, node_nb, cuckoo->nodes, &cuckoo->payload[sz]);
}

/*
 *
 */
void
cuckoo_reset(struct cuckoo_hash_s *cuckoo)
{
        cuckoo_init(cuckoo, cuckoo->max,
                    cuckoo->ctx_nb,
                    cuckoo->calc_hash,
                    cuckoo->node_init,
                    cuckoo->opt_flags);
}

/*
 *
 */
struct cuckoo_hash_s *
cuckoo_create(unsigned nb,
              unsigned ctx_nb,
              cuckoo_hash_func_t func,
              cuckoo_node_initializer_t node_init,
              unsigned flags)
{
        TRACER("nb:%u func:%p\n", nb, func);

        struct cuckoo_hash_s *cuckoo = aligned_alloc(CUCKOO_CACHELINE_SIZE, cuckoo_sizeof(nb));

        if (cuckoo)
                cuckoo_init(cuckoo, nb, ctx_nb, func, node_init, flags);

        TRACER("cuckoo:%p\n", cuckoo);
        return cuckoo;
}

/*
 *
 */
unsigned
cuckoo_max_node(const struct cuckoo_hash_s *cuckoo)
{
        return cuckoo->max;
}

/*
 *
 */
unsigned
cuckoo_used_num(const struct cuckoo_hash_s *cuckoo)
{
        return cuckoo->idx_pool->nb_used;
}

/*
 *
 */
unsigned
cuckoo_empty_num(const struct cuckoo_hash_s *cuckoo)
{
        return cuckoo->max - cuckoo->idx_pool->nb_used;
}

/*
 *
 */
static int
walk_default(struct cuckoo_hash_s *cuckoo,
             struct cuckoo_node_s *node,
             void *arg)
{
        unsigned *nb_p = arg;
        int ret = 0;
        char title[80];

        if (cuckoo_used_num(cuckoo) < *nb_p)
                ret = -1;

        snprintf(title, sizeof(title), "Walk Node %d", *nb_p);
        cuckoo_node_dump(cuckoo, stdout, title, node);

        return ret;
}

/*
 * tail to head order
 */
int
cuckoo_walk(struct cuckoo_hash_s *cuckoo,
            int (*cb_func)(struct cuckoo_hash_s *, struct cuckoo_node_s *, void *),
            void *arg)
{
        struct cuckoo_node_s *node, *next;
        unsigned nb = 0;
        int ret = 0;

        if (!cb_func) {
                cb_func = walk_default;
                arg = &nb;
        }

        IDXQ_FOREACH_REVERSE_SAFE(node, &cuckoo->used_fifo, entry, next) {
                ret = cb_func(cuckoo, node, arg);
                if (ret)
                        goto end;
                nb += 1;
        }
        if (nb != cuckoo_used_num(cuckoo))
                ret = -1;
 end:
        return ret;
}

/***************************************************************************************************
 * Delete bulk
 ***************************************************************************************************/
/*
 *
 */
enum cuckoo_del_state_e {
        CUCKOO_DEL_STATE_WAIT2,
        CUCKOO_DEL_STATE_WAIT1,

        CUCKOO_DEL_STATE_PREFETCH_NODE,
        CUCKOO_DEL_STATE_PREFETCH_BK,
        CUCKOO_DEL_STATE_CLEAN,

        CUCKOO_DEL_STATE_DONE,
        CUCKOO_DEL_STATE_NB,
};

/*
 *
 */
struct cuckoo_del_ctx_s {
        struct cuckoo_node_s *node;

        unsigned idx;
        enum cuckoo_del_state_e state;
};

/*
 *
 */
struct cuckoo_del_engine_s {
        struct cuckoo_del_ctx_s ctx_pool[3 * 5];

        struct cuckoo_node_s **node_pp;
        unsigned deleted_nb;
        unsigned next;
};

/*
 *
 */
always_inline void
init_del_engine(struct cuckoo_del_engine_s *engine,
                struct cuckoo_node_s **node_pp)
{
        engine->node_pp = node_pp;
        engine->deleted_nb = 0;
        engine->next = 0;

        for (unsigned i = 0; i < ARRAYOF(engine->ctx_pool); i++) {
                struct cuckoo_del_ctx_s *ctx = &engine->ctx_pool[i];

                switch (i % 3) {
                case 0:
                        ctx->state = CUCKOO_DEL_STATE_PREFETCH_NODE;
                        break;
                case 1:
                        ctx->state = CUCKOO_DEL_STATE_WAIT1;
                        break;
                case 2:
                        ctx->state = CUCKOO_DEL_STATE_WAIT2;
                        break;
                }
        }
}

/*
 *
 */
always_inline unsigned
do_del_ctx(struct cuckoo_hash_s *cuckoo,
           struct cuckoo_del_engine_s *engine,
           unsigned nb,
           struct cuckoo_del_ctx_s *ctx)
{
        unsigned done = 0;

        switch (ctx->state) {
        case CUCKOO_DEL_STATE_WAIT2:
                if (engine->next < nb)
                        ctx->state = CUCKOO_DEL_STATE_WAIT2;
                else
                        ctx->state = CUCKOO_DEL_STATE_DONE;
                break;

        case CUCKOO_DEL_STATE_WAIT1:
                if (engine->next < nb)
                        ctx->state = CUCKOO_DEL_STATE_PREFETCH_NODE;
                else
                        ctx->state = CUCKOO_DEL_STATE_DONE;
                break;

        case CUCKOO_DEL_STATE_PREFETCH_NODE:
        retry1:
                if (engine->next < nb) {
                        ctx->idx = engine->next++;
                        ctx->node = engine->node_pp[ctx->idx];
                        if (!ctx->node) {
                                done += 1;
                                goto retry1;
                        }

                        prefetch(ctx->node, 3);
                        ctx->state = CUCKOO_DEL_STATE_PREFETCH_BK;
                } else {
                        ctx->state = CUCKOO_DEL_STATE_DONE;
                }
                break;

        case CUCKOO_DEL_STATE_PREFETCH_BK:
                prefetch_neighbor(cuckoo, ctx->node);

                /* for prefetch, not used */
                fetch_bucket(cuckoo, hash2idx(cuckoo, ctx->node->key.hash, 0));
                fetch_bucket(cuckoo, hash2idx(cuckoo, ctx->node->key.hash, 1));

                ctx->state = CUCKOO_DEL_STATE_CLEAN;
                break;

        case CUCKOO_DEL_STATE_CLEAN:
                {
                        unsigned pos = -1;
                        struct cuckoo_bucket_s *bk;

                        bk = fetch_cuckoo_current_bucket(cuckoo, ctx->node, &pos);
                        if (bk) {
                                IDXQ_REMOVE(&cuckoo->used_fifo, ctx->node, entry);
                                bk->idx[pos] = CUCKOO_INVALID_IDX;
                                bk->hval[pos] = CUCKOO_INVALID_HVAL;
                        }
                        idx_pool_free(cuckoo, node_idx(cuckoo, ctx->node));
                        engine->deleted_nb += 1;
                        done += 1;

                retry2:
                        if (engine->next < nb) {
                                ctx->idx = engine->next++;
                                ctx->node = engine->node_pp[ctx->idx];
                                if (!ctx->node) {
                                        done += 1;
                                        goto retry2;
                                }

                                prefetch(ctx->node, 3);
                                ctx->state = CUCKOO_DEL_STATE_PREFETCH_BK;
                        } else {
                                ctx->state = CUCKOO_DEL_STATE_DONE;
                        }
                }
                break;

        case CUCKOO_DEL_STATE_DONE:
        default:
                break;
        }
        return done;
}

/*
 *
 */
always_inline unsigned
del_engine(struct cuckoo_hash_s *cuckoo,
           struct cuckoo_del_engine_s *engine,
           unsigned nb)
{
        unsigned done_nb = 0;

        while (nb > done_nb) {
                for (unsigned i = 0; (nb > done_nb) && (i < ARRAYOF(engine->ctx_pool)); i++) {
                        done_nb += do_del_ctx(cuckoo, engine, nb, &engine->ctx_pool[i]);
                }
        }
        return engine->deleted_nb;
}

/*
 *
 */
unsigned
cuckoo_del_bulk(struct cuckoo_hash_s *cuckoo,
                struct cuckoo_node_s **node_pp,
                unsigned nb)
{
        struct cuckoo_del_engine_s engine _CUCKOO_CACHE_ALIGNED;

        init_del_engine(&engine, node_pp);

        return del_engine(cuckoo, &engine, nb);
}

/***************************************************************************************************
 * Hash bulk
 ***************************************************************************************************/
/*
 *
 */
enum cuckoo_hash_state_e {
        CUCKOO_HASH_STATE_WAIT,
        CUCKOO_HASH_STATE_PREFETCH,
        CUCKOO_HASH_STATE_CALC,
        CUCKOO_HASH_STATE_DONE,

        CUCKOO_HASH_STATE_NB,
};

/*
 *
 */
struct cuckoo_hash_ctx_s {
        struct cuckoo_key_s *key_p;
        unsigned idx;
        enum cuckoo_hash_state_e state;
};

/*
 *
 */
struct cuckoo_hash_engine_s {
        struct cuckoo_hash_ctx_s ctx_pool[28];

        cuckoo_hash_func_t calc_hash;
        struct cuckoo_key_s **key_pp;
        unsigned mask;
        unsigned next;
};

/*
 *
 */
always_inline void
init_hash_engine(struct cuckoo_hash_engine_s *engine,
                 cuckoo_hash_func_t hash_func,
                 struct cuckoo_key_s **key_pp,
                 unsigned mask)
{
        engine->calc_hash = hash_func;
        engine->key_pp = key_pp;
        engine->mask = mask;
        engine->next = 0;

        for (unsigned i = 0; i < ARRAYOF(engine->ctx_pool); i++) {
                struct cuckoo_hash_ctx_s *ctx = &engine->ctx_pool[i];

                if (i % 2)
                        ctx->state = CUCKOO_HASH_STATE_PREFETCH;
                else
                        ctx->state = CUCKOO_HASH_STATE_WAIT;
        }
}

/*
 *
 */
always_inline unsigned
do_hash_ctx(struct cuckoo_hash_engine_s *engine,
            unsigned nb,
            struct cuckoo_hash_ctx_s *ctx)
{
        unsigned done = 0;

        switch (ctx->state) {
        case CUCKOO_HASH_STATE_WAIT:
                ctx->state = CUCKOO_HASH_STATE_PREFETCH;
                break;

        case CUCKOO_HASH_STATE_PREFETCH:
                if (engine->next < nb) {
                        ctx->idx = engine->next++;
                        ctx->key_p = engine->key_pp[ctx->idx];
                        prefetch(ctx->key_p, 3);
                        ctx->state = CUCKOO_HASH_STATE_CALC;
                } else {
                        ctx->state = CUCKOO_HASH_STATE_DONE;
                }
                break;

        case CUCKOO_HASH_STATE_CALC:
                ctx->key_p->hash = engine->calc_hash(ctx->key_p, engine->mask);
                ctx->state = CUCKOO_HASH_STATE_PREFETCH;
                done = 1;
                break;

        case CUCKOO_HASH_STATE_DONE:
        default:
                break;
        }
        return done;
}

/*
 *
 */
always_inline void
hash_engine(struct cuckoo_hash_engine_s *engine,
            unsigned nb)
{
        unsigned done_nb = 0;

        while (nb > done_nb) {
                for (unsigned i = 0; (nb > done_nb) && (i < ARRAYOF(engine->ctx_pool)); i++) {
                        done_nb += do_hash_ctx(engine, nb, &engine->ctx_pool[i]);
                }
        }
}

/*
 *
 */
void
cuckoo_hash_bulk(struct cuckoo_hash_s *cuckoo,
                 struct cuckoo_key_s **key_pp,
                 unsigned nb)
{
        struct cuckoo_hash_engine_s engine;

        init_hash_engine(&engine, cuckoo->calc_hash, key_pp, cuckoo->bk_mask);
        hash_engine(&engine, nb);
}

/***************************************************************************************************
 * etc tools
 ***************************************************************************************************/
/*
 *
 */
int
cuckoo_flipflop(const struct cuckoo_hash_s *cuckoo,
                const struct cuckoo_node_s *node)
{
        int ret = -1;
        uint32_t idx = node_idx(cuckoo, node);
        if (idx != CUCKOO_INVALID_IDX) {
                unsigned pos = -1;
                struct cuckoo_bucket_s *bk = fetch_cuckoo_current_bucket(cuckoo, node, &pos);

                if (bk)
                        ret = flipflop_bucket(cuckoo, NULL, bk, pos);
        }
        return ret;
}

/*
 *
 */
void
cuckoo_key_dump(const struct cuckoo_hash_s *cuckoo,
                const struct cuckoo_key_s *key,
                FILE *stream,
                const char *title)
{
        char msg[256];
        unsigned len;
        union cuckoo_hash_u hash = cuckoo_calc_hash(cuckoo, key);

        len = snprintf(msg, sizeof(msg), "%s hval:%08x key:", title,  hash2val(hash));
        for (unsigned i = 0; i < ARRAYOF(key->val.d32); i++)
                snprintf(&msg[len], sizeof(msg) - len, "%08x ", key->val.d32[i]);
        fprintf(stream, "%s\n", msg);
}

/*
 *
 */
void
cuckoo_node_dump(const struct cuckoo_hash_s *cuckoo,
                 FILE *stream,
                 const char *title,
                 const struct cuckoo_node_s *node)
{
        fprintf(stream, "%s node:%u\n", title, node_idx(cuckoo, node));
        cuckoo_key_dump(cuckoo, &node->key, stream, "--->");
}

/*
 *
 */
void
cuckoo_bucket_dump(const struct cuckoo_hash_s *cuckoo,
                   FILE *stream,
                   const char *title,
                   const struct cuckoo_bucket_s *bk)
{
        fprintf(stream,
                "%s bk:%u\n"
                "  hval:%08x %08x %08x %08x %08x %08x %08x %08x\n"
                "       %08x %08x %08x %08x %08x %08x %08x %08x\n"
                "  idx :%08x %08x %08x %08x %08x %08x %08x %08x\n"
                "       %08x %08x %08x %08x %08x %08x %08x %08x\n"
                ,
                title,
                bucket_idx(cuckoo, bk),
                bk->hval[0], bk->hval[1], bk->hval[2], bk->hval[3],
                bk->hval[4], bk->hval[5], bk->hval[6], bk->hval[7],
                bk->hval[8], bk->hval[9], bk->hval[10], bk->hval[11],
                bk->hval[12], bk->hval[13], bk->hval[14], bk->hval[15],
                bk->idx[0], bk->idx[1], bk->idx[2], bk->idx[3],
                bk->idx[4], bk->idx[5], bk->idx[6], bk->idx[7],
                bk->idx[8], bk->idx[9], bk->idx[10], bk->idx[11],
                bk->idx[12], bk->idx[13], bk->idx[14], bk->idx[15]
                );
}

/*
 *
 */
void
cuckoo_idx_pool_dump(const struct idx_pool_s *pool,
                     FILE *stream,
                     const char *title)
{
        fprintf(stream,
                "%s pool:%p size:%u nb:%u node:%p idx:%p\n",
                title, pool,
                pool->array_size,
                pool->nb_used,
                pool->node_array,
                pool->idx_array);
}

/*
 *
 */
void
cuckoo_dump(struct cuckoo_hash_s *cuckoo,
            FILE *stream,
            const char *title)
{
        uint64_t cnt = cuckoo->cnt;
        uint64_t tsc = cuckoo->tsc;

        if (!cnt)
                cnt = 1;

        fprintf(stream,
                "%s cuckoo:%p mask:%08x nb:%u max:%u ctx_nb:%u ctx_depth:%u flags:%x fails:%"PRIu64" cnt:%"PRIu64" %0.2f\n",
                title, cuckoo,
                cuckoo->bk_mask, cuckoo->nb, cuckoo->max, cuckoo->ctx_nb, cuckoo->ctx_depth,
                cuckoo->opt_flags, cuckoo->fails, cnt,
                (double) tsc / cnt);

        cuckoo_idx_pool_dump(cuckoo->idx_pool, stream, "    ");
}

/*
 *
 */
struct cuckoo_bucket_s *
cuckoo_current_bucket(const struct cuckoo_hash_s *cuckoo,
                      const struct cuckoo_node_s * node)
{
        unsigned pos = -1;
        return fetch_cuckoo_current_bucket(cuckoo, node, &pos);
}

/*
 *
 */
struct cuckoo_bucket_s *
cuckoo_another_bucket(const struct cuckoo_hash_s *cuckoo,
                      const struct cuckoo_node_s * node)
{
        struct cuckoo_bucket_s *bk = NULL;

        if (node) {
                unsigned pos = -1;
                uint32_t idx = bucket_idx(cuckoo, fetch_cuckoo_current_bucket(cuckoo, node, &pos));
                idx = (idx ^ hash2val(node->key.hash)) & cuckoo->bk_mask;
                bk = bucket_ptr(cuckoo, idx);
        }
        return bk;
}

/*
 *
 */
int
cuckoo_verify(const struct cuckoo_hash_s *cuckoo,
              const struct cuckoo_node_s *node,
              const struct cuckoo_key_s *key)
{
        int ret = -1;
        uint32_t idx = node_idx(cuckoo, node);

        if (!node) {
                fprintf(stderr, "node is NULL\n");
                goto end;
        }

        if (memcmp(&key->val, &node->key.val, sizeof(key->val))) {
                fprintf(stderr, "mismatched key. node:%u\n", idx);
                goto end;
        }

        struct cuckoo_bucket_s *cur_bk, *ano_bk;
        unsigned pos = -1;

        cur_bk = fetch_cuckoo_current_bucket(cuckoo, node, &pos);
        if (!cur_bk) {
                fprintf(stderr, "unknown current bucket. node:%u\n", idx);
                goto end;
        }

        ano_bk = fetch_cuckoo_another_bucket(cuckoo, cur_bk, pos);
        if (!ano_bk) {
                fprintf(stderr, "unknown another bucket. node:%u\n", idx);
                goto end;
        }

        union cuckoo_hash_u hash = cuckoo_calc_hash(cuckoo, &node->key);
        if (node->key.hash.val64 != hash.val64) {
                fprintf(stderr, "mismatched hash. node:%u\n", idx);
                goto end;
        }

        if (((hash2val(hash) ^ bucket_idx(cuckoo, ano_bk)) & cuckoo->bk_mask) !=
            bucket_idx(cuckoo, cur_bk)) {
                fprintf(stderr, "mismatched bucket index. node:%u\n", idx);
                goto end;
        }

        ret = 0;
 end:
        //        fprintf(stdout, "%s ret:%d\n", __func__, ret);
        return ret;
}

#if defined(ENABLE_UINIT_TEST)
/***************************************************************************************************
 * test code
 ***************************************************************************************************/
static void
speed_test_hash_bulk(struct cuckoo_hash_s *cuckoo,
                     struct cuckoo_key_s **key_pp,
                     unsigned nb)
{
        uint64_t tsc;

        cuckoo->calc_hash = GENERIC_calc_hash;
        tsc = rdtsc();
        cuckoo_hash_bulk(cuckoo, key_pp, nb);
        tsc = rdtsc() - tsc;
        fprintf(stdout, "Generic bulk hash speed %0.2f tsc/key\n", (double) tsc / nb);

        cuckoo->calc_hash = SSE42_calc_hash;
        tsc = rdtsc();
        cuckoo_hash_bulk(cuckoo, key_pp, nb);
        tsc = rdtsc() - tsc;
        fprintf(stdout, "SSE42 bulk hash speed %0.2f tsc/key\n", (double) tsc / nb);
}

static inline void
test_32x16(void)
{
        uint32_t val[16];

        for (unsigned i = 0; i < ARRAYOF(val); i++)
                val[i] = i;
        for (unsigned i = 0; i < ARRAYOF(val); i++) {
                uint64_t flags = GENERIC_find_32x16(val, i);

                if (flags != SSE41_find_32x16(val, i) ||
                    flags != AVX2_find_32x16(val, i))
                        fprintf(stdout, "Bad\n");

                fprintf(stdout, "%uth %"PRIx64"\n", i, flags);
        }
}

struct test_s {
        struct cuckoo_bucket_s bk[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_node_s node[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_find_ctx_s ctx [CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;

        struct idx_pool_s idx_pool _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_hash_s cuckoo _CUCKOO_CACHE_ALIGNED;
        uint64_t hits[1024];
};

static void
test_xxx(void)
{
        struct test_s *tbl = aligned_alloc(CUCKOO_CACHELINE_SIZE, sizeof(*tbl));
        if (tbl) {
                memset(tbl, 0, sizeof(*tbl));

                struct cuckoo_hash_s *cuckoo = &tbl->cuckoo;

                cuckoo->idx_pool = &tbl->idx_pool;
                cuckoo->nodes = tbl->node;
                cuckoo->buckets = tbl->bk;
                cuckoo->bk_mask = ARRAYOF(tbl->bk) - 1;


                for (unsigned i = 0; i < ARRAYOF(tbl->bk); i++) {
                        struct cuckoo_bucket_s *bk = &tbl->bk[i];

                        for (unsigned j = 0; j < CUCKOO_BUCKET_ENTRY_SZ; j++) {
                                bk->hval[j] = j;
                                bk->idx[j] = j;
                        }
                }

                for (unsigned k = 0; k < CUCKOO_BUCKET_ENTRY_SZ; k++) {
                        struct cuckoo_find_ctx_s *ctx = &tbl->ctx[k];

                        ctx->bk[0].ptr = bucket_ptr(cuckoo, k);
                        ctx->bk[1].ptr = bucket_ptr(cuckoo, k + CUCKOO_BUCKET_ENTRY_SZ);
                }

                uint64_t tsc;
                unsigned cnt = 0;

                /* double test */
                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < CUCKOO_BUCKET_ENTRY_SZ; j++) {
                                struct cuckoo_find_ctx_s *ctx = &tbl->ctx[j];

                                GENERIC_find_hval_in_bucket_double(cuckoo, ctx);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "Generic double speed %0.2f tsc/ctx\n", (double) tsc / cnt);

                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < CUCKOO_BUCKET_ENTRY_SZ; j++) {
                                struct cuckoo_find_ctx_s *ctx = &tbl->ctx[j];

                                SSE41_find_hval_in_bucket_double(cuckoo, ctx);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "SSE41 double speed %0.2f tsc/ctx\n", (double) tsc / cnt);

                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < CUCKOO_BUCKET_ENTRY_SZ; j++) {
                                struct cuckoo_find_ctx_s *ctx = &tbl->ctx[j];

                                AVX2_find_hval_in_bucket_double(cuckoo, ctx);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "AVX2 double speed %0.2f tsc/ctx\n", (double) tsc / cnt);


                /* single test */
                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < ARRAYOF(tbl->bk); j++) {
                                struct cuckoo_bucket_s *bk = &tbl->bk[j];

                                tbl->hits[i] += GENERIC_find_hval_in_bucket_single(cuckoo, bk, 1);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "Generic single speed %0.2f tsc/bk\n", (double) tsc / cnt);

                tsc = rdtsc();
                for (unsigned i = 0; i < ARRAYOF(tbl->hits); i++) {
                        for (unsigned j = 0; j < ARRAYOF(tbl->bk); j++) {
                                struct cuckoo_bucket_s *bk = &tbl->bk[j];

                                tbl->hits[i] += SSE41_find_hval_in_bucket_single(cuckoo, bk, 1);
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

                                tbl->hits[i] += AVX2_find_hval_in_bucket_single(cuckoo, bk, 1);
                                cnt += 1;
                        }
                }
                tsc = rdtsc() - tsc;
                fprintf(stdout, "AVX2 single speed %0.2f tsc/bk\n", (double) tsc / cnt);

                free(tbl);
        }
}

static const uint32_t HVAL[] = {
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
};

static union cuckoo_hash_u
test_hash(const struct cuckoo_key_s *key,
          uint32_t mask)
{
        union cuckoo_hash_u hash;
        uint32_t v = key->val.d32[0];

        mask = 15;

        hash.val32[1] = HVAL[v % (mask + 1)];
        hash.val32[0] = v / mask;

        fprintf(stdout, "key:%u mask:%u hash[0]:%u hash[1]:%u xor:%08x\n",
                v, mask, hash.val32[0], hash.val32[1], hash.val32[0] ^ hash.val32[1]);
        return hash;
}

static void
random_key(struct cuckoo_key_s **key_pp,
           unsigned nb)
{
        for (unsigned i = 0; i < nb; i++) {
                unsigned r = random() % nb;
                SWAP(key_pp[i], key_pp[r]);
        }
}

static void
random_node(struct cuckoo_node_s **node_pp,
            unsigned nb)
{
        for (unsigned i = 0; i < nb; i++) {
                unsigned r = random() % nb;
                SWAP(node_pp[i], node_pp[r]);
        }
}

static struct cuckoo_key_s **
init_key(unsigned nb)
{
        size_t sz = sizeof(struct cuckoo_key_s *) + sizeof(struct cuckoo_key_s);

        struct cuckoo_key_s ** array_p = calloc(nb, sz);
        struct cuckoo_key_s * array = (struct cuckoo_key_s *) &array_p[nb];
        for (unsigned i = 0; i < nb; i++)
                array_p[i] = &array[i];

        for (unsigned i = 0; i < ARRAYOF(array->val.d32); i++) {
                random_key(array_p, nb);
                for (unsigned j = 0; j < nb; j++)
                        array_p[j]->val.d32[i] = random();
        }
        random_key(array_p, nb);

        return array_p;
}

static union cuckoo_hash_u
same_hash(const struct cuckoo_key_s *key,
          uint32_t mask)
{
        union cuckoo_hash_u hash;
        (void) key;
        (void) mask;

        hash.val32[1] = 1;
        hash.val32[0] = 0;

        return hash;
}

static int
walk_countup(struct cuckoo_hash_s *cuckoo,
             struct cuckoo_node_s *n,
             void *arg)
{
        unsigned *cnt_p = arg;
        char msg[80];
        int ret = 0;

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
        cuckoo_dump(cuckoo, stdout, "All dump");

        unsigned cnt = 0;
        int n = cuckoo_walk(cuckoo, walk_countup, &cnt);

        if (n)
                fprintf(stdout, "unmatched counter n:%d cnt:%d\n", n, cuckoo_used_num(cuckoo));
        if ((unsigned) n != cuckoo_used_num(cuckoo))
                cuckoo_dump(cuckoo, stdout, "unmatched counter");
}

static int
single_add_del_test(struct cuckoo_hash_s *cuckoo,
                    struct cuckoo_key_s **key_array,
                    unsigned nb)
{
        int ret = -1;
        struct cuckoo_key_s *key = key_array[0];
        fprintf(stdout, "\n%s start %u\n\n", __func__, nb);

        fprintf(stdout, "\nADD\n");
        struct cuckoo_node_s *node = cuckoo_find_oneshot(cuckoo, key);
        struct cuckoo_bucket_s *bk_0, *bk_1;

        if (node) {
                fprintf(stdout, "ADD ok\n");
                if (cuckoo_verify(cuckoo, node, key))
                        goto end;

                bk_0 = cuckoo_current_bucket(cuckoo, node);
                bk_1 = cuckoo_another_bucket(cuckoo, node);

                cuckoo_node_dump(cuckoo, stdout, "ADD ok", node);
                cuckoo_bucket_dump(cuckoo, stdout, "ADD ok current", bk_0);
                cuckoo_bucket_dump(cuckoo, stdout, "ADD ok another", bk_1);
                cuckoo_dump(cuckoo, stdout, "ADD ok Cache");

                fprintf(stdout, "\nFlipFlop\n");
                if (cuckoo_flipflop(cuckoo, node)) {
                        fprintf(stdout, "FlipFlop ng\n");
                        goto end;
                } else {
                        fprintf(stdout, "FlipFlop ok\n");
                        if (cuckoo_verify(cuckoo, node, key))
                                goto end;
                        ret = 0;
                }

                cuckoo_node_dump(cuckoo, stdout, "FlipFlop", node);
                cuckoo_bucket_dump(cuckoo, stdout, "FlipFlop current",
                                   cuckoo_current_bucket(cuckoo, node));
                cuckoo_bucket_dump(cuckoo, stdout, "FlipFlop another",
                                   cuckoo_another_bucket(cuckoo, node));
                cuckoo_dump(cuckoo, stdout, "FlipFlop Cache");

                fprintf(stdout, "\nSearch\n");
                struct cuckoo_node_s *n = cuckoo_find_oneshot(cuckoo, key);

                cuckoo_node_dump(cuckoo, stdout, "Search", n);
                cuckoo_bucket_dump(cuckoo, stdout, "Search current",
                                   cuckoo_current_bucket(cuckoo, n));
                cuckoo_bucket_dump(cuckoo, stdout, "Search another",
                                   cuckoo_another_bucket(cuckoo, n));
                cuckoo_dump(cuckoo, stdout, "Search Cache");

                fprintf(stdout, "\nFree\n");
                cuckoo_del_oneshot(cuckoo, node);
                cuckoo_node_dump(cuckoo, stdout, "after free", node);
                cuckoo_bucket_dump(cuckoo, stdout, "after free current", bk_1);
                cuckoo_bucket_dump(cuckoo, stdout, "after free another", bk_0);
                cuckoo_dump(cuckoo, stdout, "after free Cache");

        } else {
                fprintf(stdout, "ADD ng\n");
                goto end;
        }

        ret = 0;
 end:
        fprintf(stdout, "\n");
        dump_all(cuckoo);
        fprintf(stdout, "\n%s end %d\n", __func__, ret);
        return ret;
}

/*
 * same hash key
 */
static int
collision_test(struct cuckoo_hash_s *cuckoo,
               struct cuckoo_key_s **key,
               unsigned nb)
{
        fprintf(stdout, "\n%s start %u\n", __func__, nb);

        int ret = -1;
        struct cuckoo_node_s *node[CUCKOO_BUCKET_ENTRY_SZ + 1];
        struct cuckoo_bucket_s *bk[2];

        cuckoo->calc_hash = same_hash;

        node[0] = cuckoo_find_oneshot(cuckoo, key[0]);
        bk[0] = cuckoo_current_bucket(cuckoo, node[0]);
        bk[1] = cuckoo_another_bucket(cuckoo, node[0]);

        for (unsigned i = 1; i < ARRAYOF(node); i++) {
                char title[80];

                snprintf(title, sizeof(title), "%u th", i);
                node[i] = cuckoo_find_oneshot(cuckoo, key[i]);
                if (bk[0] != cuckoo_current_bucket(cuckoo, node[i]))
                        cuckoo_flipflop(cuckoo, node[i]);

                cuckoo_bucket_dump(cuckoo, stdout, title, cuckoo_current_bucket(cuckoo, node[i]));
                if (cuckoo_verify(cuckoo, node[i], key[i]))
                        goto end;
        }

        fprintf(stdout, "nb empty slot cur:%u ano:%u\n",
                cuckoo_bk_empty_nb(cuckoo, bk[0]), cuckoo_bk_empty_nb(cuckoo, bk[1]));

        if (cuckoo_flipflop(cuckoo, node[ARRAYOF(node) - 1]) &&
            cuckoo_bk_empty_nb(cuckoo, cuckoo_another_bucket(cuckoo, node[ARRAYOF(node) - 1])) == 0) {
                fprintf(stdout, "failed to filpflop Last (ok)\n");
        } else {
                fprintf(stdout, "success to filpflop Last (why)\n");
                goto end;
        }
        if (cuckoo_verify(cuckoo, node[ARRAYOF(node) - 1], key[ARRAYOF(node) - 1]))
                goto end;

        if (cuckoo_flipflop(cuckoo, node[0])) {
                fprintf(stdout, "failed to filpflop Top (ng)\n");
                goto end;
        }
        if (cuckoo_verify(cuckoo, node[0], key[0]))
                goto end;
        if (cuckoo_flipflop(cuckoo, node[ARRAYOF(node) - 1])) {
                fprintf(stdout, "failed to filpflop Last (ng)\n");
                goto end;
        }
        if (cuckoo_verify(cuckoo, node[ARRAYOF(node) - 1], key[ARRAYOF(node) - 1]))
                goto end;

        cuckoo_bucket_dump(cuckoo, stdout, "current Top", cuckoo_current_bucket(cuckoo, node[0]));
        cuckoo_bucket_dump(cuckoo, stdout, "another Top", cuckoo_another_bucket(cuckoo, node[0]));

        ret = 0;
 end:
        fprintf(stdout, "%s ret:%d\n", __func__, ret);
        cuckoo_reset(cuckoo);
        return ret;
}

static int
verify_cb(struct cuckoo_hash_s *cuckoo,
          struct cuckoo_node_s *node,
          void *arg)
{
        struct cuckoo_key_s **key_pp = arg;

        return cuckoo_verify(cuckoo, node, key_pp[node->test_id]);
}


static int
verify_all(struct cuckoo_hash_s *cuckoo,
           struct cuckoo_key_s **key_pp,
           unsigned nb)
{
        int ret = -1;

        if (cuckoo_walk(cuckoo, verify_cb, key_pp)) {
                fprintf(stderr, "Bad walk\n");
                goto end;
        }
        if (nb != cuckoo_used_num(cuckoo)) {
                fprintf(stderr, "mismatched NB. nb:%u num+%u\n", nb, cuckoo_used_num(cuckoo));
                goto end;
        }
        ret = 0;
 end:
        return ret;
}

static int
max_test(struct cuckoo_hash_s *cuckoo,
         struct cuckoo_key_s **key_pp,
         unsigned nb)
{
        fprintf(stdout, "\n%s start %u\n", __func__, nb);

        int ret = -1;
        struct cuckoo_node_s **node = calloc(cuckoo->nb, sizeof(*node));
        struct cuckoo_node_s **n2 = calloc(cuckoo->nb, sizeof(*n2));

        cuckoo->cnt = 0;
        cuckoo->tsc = 0;

        /* bulk without hash */
        unsigned n = cuckoo_find_bulk(cuckoo,
                                      (const struct cuckoo_key_s * const *) key_pp,
                                      cuckoo->nb, node, 0);
        unsigned count = 0;
        for (unsigned i = 0; i < cuckoo->nb; i++) {
                if (node[i]) {
                        node[i]->test_id = i;
                        count++;
                }
        }

        if (n != count || n != cuckoo_used_num(cuckoo)) {
                fprintf(stdout, "mismatched NB. n:%u num:%u count:%u\n",
                        n, cuckoo_used_num(cuckoo), count);
                goto end;
        }

        fprintf(stdout, "success %u %.03f \n", n, (double) n / cuckoo->nb * 100);
        cuckoo_dump(cuckoo, stdout, "Bulk without hash Added");

        if (verify_all(cuckoo, key_pp, count)) {
                fprintf(stdout, "Error\n");
                goto end;
        }

        if (count != cuckoo_used_num(cuckoo)) {
                fprintf(stdout, "Bulk(w) unmatched num: n=%u nb=%u count=%u\n",
                       n, cuckoo_used_num(cuckoo), count);
                goto end;
        }

        cuckoo->is_debug = false;
        unsigned m = cuckoo_find_bulk(cuckoo, (const struct cuckoo_key_s * const *) key_pp,
                                      cuckoo->nb, n2, 0);
        if (n != m) {
                fprintf(stdout, "mismatched found keys m:%u n:%u\n", m, n);
                goto end;
        }
        for (unsigned i = 0; i < cuckoo->nb; i++) {
                if (node[i] != n2[i]) {
                        fprintf(stdout, "mismatched node %u\n", i);
                        goto end;
                }
        }
        cuckoo->is_debug = false;

        fprintf(stdout, "start free\n");
        random_node(node, cuckoo->nb);
        uint64_t tsc = rdtsc();
        unsigned del_nb = cuckoo_del_bulk(cuckoo, node, cuckoo->nb);
        if (del_nb != m) {
                fprintf(stdout, "mismatched deleted m:%u del:%u\n", m, del_nb);
                goto end;
        }
        fprintf(stdout, "delete %0.2f tsc/del\n", (double) (rdtsc() - tsc) / del_nb);

        cuckoo_dump(cuckoo, stdout, "Free node");
        ret = 0;
 end:
        cuckoo_reset(cuckoo);
        free(node);
        free(n2);
        return ret;
}

static double
speed_sub_sub(struct cuckoo_hash_s *cuckoo,
              struct cuckoo_key_s **key_pp,
              unsigned nb,
              int with_hash)
{
        struct cuckoo_key_s key[256];
        struct cuckoo_node_s *node[256];
        struct cuckoo_key_s *key_p[256];
        double tsc = 0;

        uint64_t start_cnt = cuckoo->cnt;
        uint64_t start_tsc = cuckoo->tsc;

        for (unsigned k = 0; k < ARRAYOF(key); k++)
                key_p[k] = &key[k];

        for (unsigned base = 0; base < nb; base += ARRAYOF(key)) {
                unsigned num;

                for (unsigned k = 0; k < ARRAYOF(key); k++)
                        memcpy(&key[k], key_pp[base + k], sizeof(struct cuckoo_key_s));

                if (with_hash)
                        for (unsigned k = 0; k < ARRAYOF(key); k++)
                                key[k].hash = cuckoo_calc_hash(cuckoo, &key[k]);

                num = cuckoo_find_bulk(cuckoo, (const struct cuckoo_key_s * const *) key_p,
                                       ARRAYOF(key), node, with_hash);
                if (ARRAYOF(key) != num) {
                        fprintf(stdout, "xxx Failure. num:%u base:%u\n", num, base);
                        goto end;
                }
                for (unsigned k = 0; k < ARRAYOF(key); k++)
                        key_pp[base + k]->hash = node[k]->key.hash;
        }
        tsc = (double) (cuckoo->tsc - start_tsc) / (cuckoo->cnt - start_cnt);
 end:
         return tsc;
}

static int
speed_sub(struct cuckoo_hash_s *cuckoo,
          struct cuckoo_key_s **key_pp,
          unsigned nb,
          int w_hash)
{
        double add, search;

        cuckoo_reset(cuckoo);

        random_key(key_pp, nb);
        add = speed_sub_sub(cuckoo, key_pp, nb, w_hash);
        cuckoo_dump(cuckoo, stdout, "speed add");
        fprintf(stdout, "bulk with_hash:%d add Speed n:%u %0.2f tsc/key\n", w_hash, nb, add);

        random_key(key_pp, nb);
        search = speed_sub_sub(cuckoo, key_pp, nb, w_hash);
        cuckoo_dump(cuckoo, stdout, "speed find");
        fprintf(stdout, "bulk with_hash:%d find speed n:%u %0.2f tsc/key\n\n", w_hash, nb, search);

        return 0;
}

static void
analyze_ctx_num(struct cuckoo_hash_s *cuckoo,
                struct cuckoo_key_s **key_pp,
                unsigned nb)
{
        cuckoo->opt_flags &= ~CUCKOO_DISABLE_FLAG(CUCKOO_DISABLE_LIST);

        for (unsigned i = 0; i < 2; i++) {
                for (int w_hash = 0; w_hash < 2; w_hash++) {
                        uint64_t best_tsc = UINT64_C(-1);
                        unsigned best_nb;

                        for (unsigned ctx_nb = 1; ctx_nb < 9; ctx_nb++) {
                                cuckoo->ctx_nb = ctx_nb;
                                cuckoo_reset(cuckoo);

                                random_key(key_pp, nb);
                                speed_sub_sub(cuckoo, key_pp, nb, w_hash);

                                random_key(key_pp, nb);
                                speed_sub_sub(cuckoo, key_pp, nb, w_hash);

                                if (best_tsc > cuckoo->tsc) {
                                        best_tsc = cuckoo->tsc;
                                        best_nb = ctx_nb;
                                }
                        }
                        fprintf(stdout, "with hash:%d ctx_nb:%u flags:%x\n",
                                w_hash, best_nb, cuckoo->opt_flags);
                }
                cuckoo->opt_flags |= CUCKOO_DISABLE_FLAG(CUCKOO_DISABLE_LIST);
        }
}

static int
speed_test(struct cuckoo_hash_s *cuckoo,
           struct cuckoo_key_s **key_pp,
           unsigned nb)
{

       int ret = -1;

       nb = cuckoo->max;
       nb &= ~255;

       fprintf(stdout, "\n%s start %u\n", __func__, nb);

       ret = speed_sub(cuckoo, key_pp, nb, 0);
       if (ret)
               goto end;
       ret = speed_sub(cuckoo, key_pp, nb, 1);
       if (ret)
               goto end;
 end:
       cuckoo_reset(cuckoo);

       return ret;
}

/***************************************************************************************************
 *
 ***************************************************************************************************/

int
cuckoo_test(unsigned nb,
            unsigned ctx_size,
            bool do_speed_test,
            bool do_analyze,
            bool do_unit,
            unsigned flags)
{
        fprintf(stdout, "nb:%u\n", nb);

        struct cuckoo_hash_s *cuckoo;
        cuckoo_hash_func_t calk_hash = test_hash;

        cuckoo = cuckoo_create(nb, ctx_size, NULL, NULL, flags);
        cuckoo_dump(cuckoo, stdout, "Cache");

        struct cuckoo_key_s **key = init_key(cuckoo->nb);

        SWAP(calk_hash, cuckoo->calc_hash);
        if (single_add_del_test(cuckoo, key, nb))
                goto end;

        if (collision_test(cuckoo, key, nb))
                goto end;

        SWAP(calk_hash, cuckoo->calc_hash);
        if (max_test(cuckoo, key, nb))
                goto end;

        if (do_speed_test) {
                if (speed_test(cuckoo, key, nb))
                        goto end;
        }

        if (do_analyze)
                analyze_ctx_num(cuckoo, key, nb);

        if (do_unit) {
                speed_test_hash_bulk(cuckoo, key, nb);
                test_xxx();
        }

 end:
        free(cuckoo);
        return 0;
}

#endif /* ENABLE_UINIT_TEST */
