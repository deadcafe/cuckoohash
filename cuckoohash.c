/* SPDX-License-Identifier: BSD-2-Clause
 * Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
 */

#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <sched.h>
#include <unistd.h>
#include <sys/mman.h>
#include <fcntl.h>

#if defined(ENABLE_PAPI)
# include <papi.h>
#endif

#include "cuckoohash.h"

#ifndef ARRAYOF
# define ARRAYOF(_a)     (sizeof(_a)/sizeof(_a[0]))
#endif

#ifndef SWAP
# define SWAP(a,b) do { typeof(a) _c = (a); (a) = (b); (b) = _c;} while (0)
#endif

/*
 * ceiling multiple
 */
#ifndef CEIL_MULTIPLE
# define CEIL_MULTIPLE(value, multiple) (((value) + (multiple) - 1) / (multiple) * (multiple))
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
#if defined(KEY_IS_IN_BUCKET)
        uint8_t key[CUCKOO_BUCKET_ENTRY_SZ][48];
#endif
} _CUCKOO_CACHE_ALIGNED;

/*
 *
 */
struct idx_pool_s {
        unsigned nb_idx;
        unsigned nb_used;
        uint32_t *idx_array;
};

/*
 *
 */
always_inline size_t
idx_pool_sizeof(unsigned nb,
                size_t align)
{
        size_t size = sizeof(uint32_t) * nb;

        size = CEIL_MULTIPLE(size, align);
        return size;
}

/*
 *
 */
always_inline void
idx_pool_init(struct idx_pool_s *idx_pool,
              unsigned nb,
              void *idx_array)
{
        idx_pool->nb_idx = nb;
        idx_pool->idx_array = idx_array;
        idx_pool->nb_used = 0;

        for (uint32_t idx = 0; idx < nb; idx++)
                idx_pool->idx_array[idx] = idx;
}

/*
 *
 */
always_inline uint32_t
idx_pool_alloc(struct idx_pool_s *idx_pool)
{
        uint32_t idx = IDXQ_NULL;

        if (idx_pool->nb_idx > idx_pool->nb_used) {
                idx = idx_pool->idx_array[idx_pool->nb_used++];
        }
        return idx;
}

/*
 *
 */
always_inline void
idx_pool_free(struct idx_pool_s *idx_pool,
              uint32_t idx)
{
        if (idx != IDXQ_NULL) {
                idx_pool->idx_array[--(idx_pool->nb_used)] = idx;
        }
}

/*
 *
 */
always_inline unsigned
idx_pool_nb(const struct idx_pool_s *pool)
{
        return pool->nb_idx;
}

/*
 *
 */
always_inline unsigned
idx_pool_used(const struct idx_pool_s *pool)
{
        return pool->nb_used;
}

/*
 *
 */
always_inline int
idx_pool_dump(const struct idx_pool_s *pool,
              FILE *stream,
              const char *title)
{
        return fprintf(stream,
                       "<%s> pool:%p nb:%u used:%u array:%p\n",
                       title, pool,
                       pool->nb_idx,
                       pool->nb_used,
                       pool->idx_array);
}

/*
 * index table
 */
struct idx_tbl_s {
        unsigned len;	/* unit length */
        unsigned mask;	/* bit mask */
        char *base;	/* unit array pointer */
};

/*
 * index table
 */
always_inline void
idx_tbl_init(struct idx_tbl_s *idx_tbl,
             unsigned len,
             unsigned mask,
             void *array)
{
        idx_tbl->len = len;
        idx_tbl->mask = mask;
        idx_tbl->base = array;
}

/*
 * length of table element
 */
always_inline unsigned
idx_tbl_len(const struct idx_tbl_s *idx_tbl)
{
        return idx_tbl->len;
}

/*
 * element array
 */
always_inline void *
idx_tbl_array(const struct idx_tbl_s *idx_tbl)
{
        return idx_tbl->base;
}

/*
 * number of elements (must be 2^n)
 */
always_inline unsigned
idx_tbl_nb(const struct idx_tbl_s *idx_tbl)
{
        return idx_tbl->mask + 1;
}

/*
 * array index mask
 */
always_inline unsigned
idx_tbl_mask(const struct idx_tbl_s *idx_tbl)
{
        return idx_tbl->mask;
}

/*
 * index to pointer
 */
always_inline void *
idx2ptr(const struct idx_tbl_s *idx_tbl,
        unsigned idx)
{
        if (idx == IDXQ_NULL)
                return NULL;
        idx &= idx_tbl->mask;
        return &idx_tbl->base[idx * idx_tbl->len];
}

/*
 * pointer to index
 */
always_inline unsigned
ptr2idx(const struct idx_tbl_s *idx_tbl,
        const void *ptr)
{
        if (!ptr)
                return IDXQ_NULL;
        return (((char *) ptr) - idx_tbl->base) / idx_tbl->len;
}

/*
 * Dump index table elements
 */
always_inline int
idx_tbl_dump(const struct idx_tbl_s *tbl,
             FILE *stream,
             const char *title)
{
        return fprintf(stream, "<%s> tbl:%p len:%u mask:%08x base:%p\n",
                       title, tbl,
                       tbl->len, tbl->mask, tbl->base);
}

/*
 *
 */
#define CUCKOO_PIPELIN_STAGE_NB	3

enum cuckoo_find_stage_e {
        CUCKOO_FIND_STAGE_DONE = 0,

        CUCKOO_FIND_STAGE_STANDBY_3rd,	/* 3rd pipeline standing by */
        CUCKOO_FIND_STAGE_STANDBY_2th,	/* 2nd pipeline standing by */

        CUCKOO_FIND_STAGE_CALCHASH,	/* calk hash * prefetch bucket */
        CUCKOO_FIND_STAGE_FINDHVAL,	/* find HVAL in bucket & prefetch node */
        CUCKOO_FIND_STAGE_CMPKEY,	/* compare key in node */
};

/*
 *
 */
struct cuckoo_find_ctx_s {
        struct cuckoo_bucket_s *bk[2];
        uint64_t hits[2];			/* hval match flags */

        union cuckoo_hash_u hash;
        const void *key_p;
        struct cuckoo_node_s **node_pp;

        struct cuckoo_node_s *found;
        struct cuckoo_node_s *prev;
        struct cuckoo_node_s *next;

        unsigned idx;				/* request index */
        enum cuckoo_find_stage_e stage;		/* next stage */
};

/*
 *
 */
struct cuckoo_find_engine_s {
        struct cuckoo_find_ctx_s ctx_pool[CUCKOO_PIPELINE_NB] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_node_s ** node_pp;
        const void * const * key_pp;
        uint32_t *bk_idx;

        unsigned ctx_pool_size;
        unsigned next;
        unsigned req_nb;
        unsigned node_nb;
};

struct general_s {
        uint8_t _something[CUCKOO_CACHELINE_SIZE];
};


/*
 * Arch handler
 */
typedef uint64_t (*find_idx_in_bucket_t)(const struct cuckoo_hash_s *,
                                         const struct cuckoo_bucket_s *,
                                         uint32_t);
typedef uint64_t (*find_hval_in_bucket_t)(const struct cuckoo_hash_s *,
                                          const struct cuckoo_bucket_s *,
                                          uint32_t);
typedef int (*debug_fprintf_t)(FILE *stream, const char *format, ...);

IDXQ_HEAD(cuckoo_node_q_s, cuckoo_node_s);

/*
 * cuckoo_hash_s
 * idx pool
 * node array
 * bcuket array
 */
struct cuckoo_hash_s {
        unsigned ctx_nb;
        unsigned key_len;
        unsigned opt_flags;
        unsigned _reserved;

        /* tables */
        struct idx_tbl_s node_tbl;
        struct idx_tbl_s bk_tbl;
        struct idx_tbl_s user_tbl;

        /* drivers */
        cuckoo_hash_func_t calc_hash;
        find_idx_in_bucket_t find_idx;
        find_hval_in_bucket_t find_hval;
        cuckoo_user_initializer_t user_init;

        struct idx_pool_s idx_pool;

        uint64_t cnt;
        uint64_t tsc;
        uint64_t fails;

        uint64_t bkcnt[3];	/* bucket counter 0:1st 1:2nd 2:full */

        struct cuckoo_node_q_s used_fifo;
        struct cuckoo_find_engine_s engine _CUCKOO_CACHE_ALIGNED;

        char payload[] _CUCKOO_CACHE_ALIGNED;
};

/****************************************************************************************************
 *
 ****************************************************************************************************/

#if defined(ENABLE_TRACER)
/*
 *
 */
static int
null_fprintf(FILE *stream __attribute__((unused)),
             const char *format __attribute__((unused)),
             ...)
{
        return 0;
}

static debug_fprintf_t debug_fprintf = null_fprintf;

/*
 *
 */
always_inline void
set_debug_handler(const struct cuckoo_hash_s *cuckoo)
{
        if (CUCKOO_IS_DISABLE(cuckoo->opt_flags, CUCKOO_ENABLE_DEBUG))
                debug_fprintf = fprintf;
}

/*
 *
 */
always_inline void
cls_debug_handler(const struct cuckoo_hash_s *cuckoo)
{
        if (CUCKOO_IS_DISABLE(cuckoo->opt_flags, CUCKOO_ENABLE_DEBUG))
                debug_fprintf = null_fprintf;
}

# define TRACER(fmt,...)        debug_fprintf(stderr, "%s():%d " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
# define TRACER(fmt,...)

//static debug_fprintf_t debug_fprintf = null_fprintf;

/*
 *
 */
always_inline void
set_debug_handler(const struct cuckoo_hash_s *cuckoo __attribute__((unused)))
{
        ;
}

/*
 *
 */
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
prefetch(const volatile void *p,
         const int locality)
{
#if 1
        __builtin_prefetch((const void *) p, 0, locality);
#else
        //        asm volatile ("prefetcht0 %[p]" : : [p] "m" (*(const volatile char *) p));
        (void) p;
        (void) locality;
#endif
}

/*
 * Read Timestamp Counter (x86 only)
 */
always_inline uint64_t
rdtsc(void)
{
        return __builtin_ia32_rdtsc();
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
        return (hash.val32[even_odd] & idx_tbl_mask(&cuckoo->bk_tbl));
}

/*
 *
 */
always_inline unsigned
bucket_idx(const struct cuckoo_hash_s *cuckoo,
           const struct cuckoo_bucket_s *bk)
{
        return ptr2idx(&cuckoo->bk_tbl, bk);
}

/*
 *
 */
always_inline struct cuckoo_bucket_s *
bucket_ptr(const struct cuckoo_hash_s *cuckoo,
           uint32_t idx)
{
        return idx2ptr(&cuckoo->bk_tbl, idx);
}

/*
 *
 */
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
        uint32_t idx = ((bucket_idx(cuckoo, bk) ^ hval) & idx_tbl_mask(&cuckoo->bk_tbl));

        return fetch_bucket(cuckoo, idx);
}

/*
 *
 */
always_inline uint32_t
node_idx(const struct cuckoo_hash_s *cuckoo,
         const struct cuckoo_node_s *node)
{
        return ptr2idx(&cuckoo->node_tbl, node);
}

/*
 *
 */
always_inline struct cuckoo_node_s *
node_ptr(const struct cuckoo_hash_s *cuckoo,
         uint32_t idx)
{
        return idx2ptr(&cuckoo->node_tbl, idx);
}

/*
 *
 */
always_inline void
idx_pool_prefetch(const struct idx_pool_s *pool)
{
        prefetch(&pool->idx_array[pool->nb_used], 3);
}

/*
 *
 */
always_inline void
idx_pool_next_prefetch(const struct cuckoo_hash_s *cuckoo,
                       unsigned nb)
{
        const struct idx_pool_s *pool = &cuckoo->idx_pool;
        unsigned top = pool->nb_used;
        unsigned tail = top + nb;

        if (tail >= pool->nb_idx)
                tail = pool->nb_idx;

        for (unsigned i = top; i < tail; i++) {
                unsigned idx = pool->idx_array[i];

                prefetch(node_ptr(cuckoo, idx), 3);
        }
}

#if defined(KEY_IS_IN_BUCKET)
/*
 *
 */
always_inline uint8_t *
get_key_in_bucket(const struct cuckoo_hash_s *cuckoo __attribute__((unused)),
                  struct cuckoo_bucket_s *bk,
                  unsigned pos)
{
        return &bk->key[pos][0];
}
#define GET_KEY(cuckoo, bk, pos)	get_key_in_bucket((cuckoo), (bk), (pos))
#else
/*
 *
 */
always_inline void *
get_key_in_node(const struct cuckoo_hash_s *cuckoo,
                struct cuckoo_bucket_s *bk,
                unsigned pos)
{
        struct cuckoo_node_s *node = node_ptr(cuckoo, bk->idx[pos]);

        return &node->key[0];
}
#define GET_KEY(cuckoo, bk, pos)	get_key_in_node((cuckoo), (bk), (pos))
#endif

/*
 *
 */
always_inline int
cmp_key(const struct cuckoo_hash_s *cuckoo,
        const uint8_t *a,
        const uint8_t *b)
{
        return memcmp(a, b, cuckoo->key_len);
}

/*
 *
 */
always_inline void
copy_key(const struct cuckoo_hash_s *cuckoo,
         void *dst,
         const void *src)
{
        memcpy(dst, src, cuckoo->key_len);
}

/*
 *
 */
always_inline void
prefetch_key(const struct cuckoo_hash_s *cuckoo,
             struct cuckoo_bucket_s *bk,
             uint64_t hits)
{
        unsigned pos = __builtin_ctzll(hits);

        for (hits >>= pos; hits; pos++, hits >>= 1) {
                if (hits & 1) {
                        prefetch(GET_KEY(cuckoo, bk, pos), 3);
                        prefetch(node_ptr(cuckoo, bk->idx[pos]), 2);
                }
        }
}

#define BUCKET_DRIVER_GENERATE(name)                                    \
static inline uint64_t                                          	\
name##_find_idx_in_bucket(const struct cuckoo_hash_s *cuckoo,           \
                          const struct cuckoo_bucket_s * bk,            \
                          uint32_t idx)                                 \
{                                                                       \
	(void) cuckoo;                                                  \
        TRACER("bk:%u\n"                                                \
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          \
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          \
               "idx:%08x\n",                                            \
               bucket_idx(cuckoo, bk),                                  \
               bk->idx[0], bk->idx[1], bk->idx[2], bk->idx[3],          \
               bk->idx[4], bk->idx[5], bk->idx[6], bk->idx[7],          \
               bk->idx[8], bk->idx[9], bk->idx[10], bk->idx[11],        \
               bk->idx[12], bk->idx[13], bk->idx[14], bk->idx[15],      \
               idx);                                                    \
        uint64_t flags = name##_find_32x16(bk->idx, idx);               \
        TRACER("flags:%04x\n", flags);                                  \
        return flags;                                                   \
}                                                                       \
static inline uint64_t                                                  \
name##_find_hval_in_bucket(const struct cuckoo_hash_s *cuckoo,   	\
                           const struct cuckoo_bucket_s *bk,     	\
                           uint32_t hval)                        	\
{                                                                       \
        (void) cuckoo;                                                  \
        TRACER("bk:%u\n"                                                \
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          \
               "    %08x %08x %08x %08x %08x %08x %08x %08x\n"          \
               "hval:%08x\n",                                           \
               bucket_idx(cuckoo, bk),                                  \
               bk->hval[0], bk->hval[1], bk->hval[2], bk->hval[3],      \
               bk->hval[4], bk->hval[5], bk->hval[6], bk->hval[7],      \
               bk->hval[8], bk->hval[9], bk->hval[10], bk->hval[11],    \
               bk->hval[12], bk->hval[13], bk->hval[14], bk->hval[15],  \
               hval);                                                   \
        uint64_t flags = name##_find_32x16(bk->hval, hval);             \
        TRACER("flags:%04x\n", flags);                                  \
        return flags;                                                   \
}

/*****************************************************************************
 * default Handler -->
 *****************************************************************************/
/*
 *
 */
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
GENERIC_calc_hash(const void *key,
                  unsigned key_len,
                  uint32_t mask)
{
        union cuckoo_hash_u hash;
        const uint32_t *d32 = key;
        unsigned size = key_len / sizeof(*d32);

        hash.val32[0] = 0;
        hash.val32[1] = 0xdeadbeef;

        for (unsigned i = 0; i < size; i += 2) {
                hash.val32[0] = murmurhash3_32(&d32[i], 2, hash.val32[0]);
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

BUCKET_DRIVER_GENERATE(GENERIC);

/*****************************************************************************
 * <-- default Handler
 *****************************************************************************/

#if defined(__x86_64__)
#include <x86intrin.h>
#include <cpuid.h>

always_inline void
cacheline_flush(const void * ptr)
{
#if 1
                _mm_clflushopt((void *) ptr);
#else
                asm volatile ("clflushopt (%0)" :: "r" ptr : "memory");
#endif
}

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
SSE42_calc_hash(const void *key,
                unsigned len,
                uint32_t mask)
{
        union cuckoo_hash_u hash;
        const uint64_t *d64 = key;
        unsigned size = len / sizeof(*d64);

        hash.val32[0] = 0;
        hash.val32[1] = 0xdeadbeef;

        for (unsigned i = 0; i < size; i++) {
                hash.val32[0] = _mm_crc32_u64(hash.val32[0], d64[i]);
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

                        cuckoo->find_idx  = SSE41_find_idx_in_bucket;
                        cuckoo->find_hval = SSE41_find_hval_in_bucket;
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

                        cuckoo->find_idx  = AVX2_find_idx_in_bucket;
                        cuckoo->find_hval = AVX2_find_hval_in_bucket;
                }
#endif

#if defined(__AVX512F__)
                if (!CUCKOO_IS_DISABLE(flags, CUCKOO_DISABLE_AVX512) && (ebx & bit_AVX512F)) {
                        TRACER("use AVX512F ready\n");

                        cuckoo->find_idx  = AVX512_find_idx_in_bucket;
                        cuckoo->find_hval = AVX512_find_hval_in_bucket;
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
        cuckoo->find_idx  = NEON_find_idx_in_bucket;
        cuckoo->find_hval = NEON_find_hval_in_bucket;
}
#endif /* __ARM_NEON__ */


/*
 *
 */
always_inline struct cuckoo_bucket_s *
fetch_cuckoo_current_bucket(const struct cuckoo_hash_s *cuckoo,
                            const struct cuckoo_node_s *node,
                            unsigned *pos_p)
{
        union cuckoo_hash_u hash = node->hash;
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
        uint64_t mask = cuckoo->find_hval(cuckoo, bk, CUCKOO_INVALID_HVAL);

        return __builtin_popcountll(mask);
}

/*
 *
 */
always_inline void
reset_bucket_hits(struct cuckoo_find_engine_s *engine,
                  const struct cuckoo_bucket_s *bk)
{
        for (unsigned i = 0; i < engine->ctx_pool_size; i++) {
                struct cuckoo_find_ctx_s *ctx = &engine->ctx_pool[i];

                if (ctx->stage != CUCKOO_FIND_STAGE_CMPKEY)
                        continue;

                if (ctx->bk[0] == bk || ctx->bk[1] == bk) {
                        ctx->hits[0] = CUCKOO_INVALID_FLAGS;
                        ctx->hits[1] = CUCKOO_INVALID_FLAGS;
                }
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
nb_nodes (unsigned org)
{
        unsigned nb_entries = org;

        if (nb_entries < CUCKOO_NB_ENTRIES_MIN)
                nb_entries = CUCKOO_NB_ENTRIES_MIN;
        nb_entries = align_pow2(nb_entries);
        if (nb_entries < (org * CUCKOO_BUCKET_ENTRY_SZ) / CUCKOO_COEF)
                nb_entries <<= 1;

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

        uint64_t empty = cuckoo->find_hval(cuckoo, dst_bk, CUCKOO_INVALID_HVAL);
        if (empty) {
                dst_pos = __builtin_ctzll(empty);

#if defined(KEY_IS_IN_BUCKET)
                /* move bucket */
                copy_key(cuckoo,
                         GET_KEY(cuckoo, dst_bk, dst_pos),
                         GET_KEY(cuckoo, src_bk, src_pos));
#endif

                dst_bk->hval[dst_pos] = src_bk->hval[src_pos];
                dst_bk->idx[dst_pos] = src_bk->idx[src_pos];

                /* clear src */
                src_bk->hval[src_pos] = CUCKOO_INVALID_HVAL;
                src_bk->idx[src_pos] = CUCKOO_INVALID_IDX;

                if (engine) {
                        reset_bucket_hits(engine, dst_bk);
                        reset_bucket_hits(engine, src_bk);
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
kickout_node(struct cuckoo_hash_s *cuckoo,
             struct cuckoo_find_engine_s *engine,
             struct cuckoo_bucket_s *bk,
             int cnt)
{
        int pos = -1;

        cuckoo->bkcnt[2] += 1;

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
                    struct cuckoo_bucket_s *bk,
                    uint64_t hits,
                    const uint8_t *key,
                    unsigned *pos_p)
{
        struct cuckoo_node_s *node = NULL;
        unsigned pos = -1;

        TRACER("bk:%u key:%p hits:%"PRIx64"\n", bucket_idx(cuckoo, bk), key, hits);

        if (hits) {
                pos = __builtin_ctzll(hits);
                for (hits >>= pos; hits; pos++, hits >>= 1) {
                        if (hits & 1) {
                                const uint8_t *k = GET_KEY(cuckoo, bk, pos);
                                if (!cmp_key(cuckoo, k, key)) {
                                        node = node_ptr(cuckoo, bk->idx[pos]);
                                        *pos_p = pos;
                                        break;
                                }
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
               bucket_idx(cuckoo, ctx->bk[0]), bucket_idx(cuckoo, ctx->bk[1]),
               hash2val(ctx->hash));

        uint64_t empt[2];
        empt[0] = cuckoo->find_hval(cuckoo, ctx->bk[0], CUCKOO_INVALID_HVAL);
        if (!empt[0])
                empt[1] = cuckoo->find_hval(cuckoo, ctx->bk[1], CUCKOO_INVALID_HVAL);

        if (empt[0]) {
                bk = ctx->bk[0];
                pos = __builtin_ctzll(empt[0]);
        } else if (empt[1]) {
                bk = ctx->bk[1];
                pos = __builtin_ctzll(empt[1]);
        } else {
                /* No Vacancy */
                pos = kickout_node(cuckoo, engine, ctx->bk[0], CUCKOO_FIND_DEPTH);
                if (pos < 0) {
                        pos = kickout_node(cuckoo, engine, ctx->bk[1], CUCKOO_FIND_DEPTH);
                        if (pos < 0) {
                                /* error */
                                TRACER("failed to insert node\n");
                                goto end;
                        }
                        bk = ctx->bk[1];
                } else {
                        bk = ctx->bk[0];
                }
        }
        TRACER("bk:%u pos:%u\n", bucket_idx(cuckoo, bk), pos);

        node_idx = idx_pool_alloc(&cuckoo->idx_pool);
        if (node_idx != CUCKOO_INVALID_IDX) {
                if (cuckoo->user_init(idx2ptr(&cuckoo->user_tbl, node_idx),
                                      idx_tbl_len(&cuckoo->user_tbl),
                                      ctx->key_p, cuckoo->key_len)) {
                        /* failed to init user data */
                        idx_pool_free(&cuckoo->idx_pool, node_idx);

                        TRACER("not inserted node:%u\n", node_idx);
                        node_idx = CUCKOO_INVALID_IDX;
                } else {
                        /* set bucket */
                        bk->hval[pos] = hash2val(ctx->hash);
                        bk->idx[pos] = node_idx;
                        copy_key(cuckoo, GET_KEY(cuckoo, bk, pos), ctx->key_p);

                        /* set node */
                        node_ptr(cuckoo, node_idx)->hash = ctx->hash;

                        reset_bucket_hits(engine, bk);
                        TRACER("node:%u bk:%u pos:%d\n", node_idx, bucket_idx(cuckoo, bk), pos);
                }
        } else {
                TRACER("User data is full\n");
        }
 end:
        return node_ptr(cuckoo, node_idx);
}

always_inline int
list_node(struct cuckoo_hash_s *cuckoo,
          struct cuckoo_find_ctx_s *ctx)
{
        int ret = 0;

        if (ctx->found) {
               IDXQ_REMOVE(&cuckoo->used_fifo, ctx->found, entry);
               IDXQ_INSERT_HEAD(&cuckoo->used_fifo, ctx->found, entry);
               ctx->found = NULL;
#if 0
               if (ctx->prev)
                       cacheline_flush(ctx->prev);

               if (ctx->next)
                       cacheline_flush(ctx->next);
#endif
               ret = 1;
        }
        return ret;
}

/*
 * prefetch neighbor node in used node queue
 */
always_inline void
prefetch_neighbor(const struct cuckoo_hash_s *cuckoo,
                  struct cuckoo_find_ctx_s *ctx,
                  struct cuckoo_node_s *node)
{
        ctx->found = node;

        if ((ctx->prev = IDXQ_PREV(&cuckoo->used_fifo, node, entry)) != NULL)
                 prefetch(ctx->prev, 3);

        if ((ctx->next = IDXQ_PREV(&cuckoo->used_fifo, node, entry)) != NULL)
                 prefetch(ctx->next, 3);
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

        switch (ctx->stage) {
        default:
        case CUCKOO_FIND_STAGE_DONE:
                done = 1;
                break;

        case CUCKOO_FIND_STAGE_STANDBY_3rd:
        case CUCKOO_FIND_STAGE_STANDBY_2th:
                if (engine->next < nb) {
                        ctx->stage = CUCKOO_FIND_STAGE_DONE;
                        done = 1;
                } else {
                        ctx->stage += 1;
                }
                break;

        case CUCKOO_FIND_STAGE_CALCHASH:
                if (engine->next < nb) {
                        ctx->idx     = engine->next++;
                        ctx->key_p   = engine->key_pp[ctx->idx];
                        ctx->node_pp = &engine->node_pp[ctx->idx];

                        /* calk hash and fetch bucket */
                        ctx->hash = cuckoo->calc_hash(ctx->key_p, cuckoo->key_len,
                                                      idx_tbl_mask(&cuckoo->bk_tbl));

                        /* do prefetch */
                        ctx->bk[0]   = fetch_bucket(cuckoo, hash2idx(cuckoo, ctx->hash, 0));
                        ctx->hits[0] = CUCKOO_INVALID_FLAGS;

                        /* not prefetch */
                        ctx->bk[1]   = bucket_ptr(cuckoo, hash2idx(cuckoo, ctx->hash, 1));
                        ctx->hits[1] = CUCKOO_INVALID_FLAGS;

                        list_node(cuckoo, ctx);
                        ctx->stage = CUCKOO_FIND_STAGE_FINDHVAL;
                } else {
                        list_node(cuckoo, ctx);

                        ctx->stage = CUCKOO_FIND_STAGE_DONE;
                        done = 1;
                }
                break;

        case CUCKOO_FIND_STAGE_FINDHVAL:
                /* find hash value in bucket */
                ctx->hits[0] = cuckoo->find_hval(cuckoo, ctx->bk[0], hash2val(ctx->hash));
                if (ctx->hits[0]) {
                        prefetch_key(cuckoo, ctx->bk[0], ctx->hits[0]);
                } else {
                        ctx->hits[1] = cuckoo->find_hval(cuckoo, ctx->bk[1], hash2val(ctx->hash));
                        if (ctx->hits[1]) {
                                prefetch_key(cuckoo, ctx->bk[1], ctx->hits[1]);
                        }
                }
                ctx->stage = CUCKOO_FIND_STAGE_CMPKEY;
                break;

        case CUCKOO_FIND_STAGE_CMPKEY:
                {
                        struct cuckoo_node_s *node = NULL;
                        unsigned pos;

                        for (unsigned i = 0; i < 2; i++) {
                                if (ctx->hits[i] == CUCKOO_INVALID_FLAGS) {
                                        ctx->hits[i] = cuckoo->find_hval(cuckoo, ctx->bk[i],
                                                                         hash2val(ctx->hash));
                                }

                                node = find_node_in_bucket(cuckoo, ctx->bk[i], ctx->hits[i],
                                                           ctx->key_p, &pos);
                                if (node) {
                                        cuckoo->bkcnt[i] += 1;
#if 1
                                        cacheline_flush(ctx->bk[i]->hval);
                                        cacheline_flush(ctx->bk[i]->idx);
#endif
                                        break;
                                }
                        }

                        if (!node) {
                                node = insert_node(cuckoo, engine, ctx);
                                if (node) {
                                        IDXQ_INSERT_HEAD(&cuckoo->used_fifo, node, entry);
                                }
                        } else {
                                if (!CUCKOO_IS_DISABLE(cuckoo->opt_flags, CUCKOO_DISABLE_LIST)) {
                                        prefetch_neighbor(cuckoo, ctx, node);
                                }
                        }

                        *ctx->node_pp = node;

                        if (node) {
                                engine->node_nb += 1;
                        } else {
                                fprintf(stdout, "xxxxxx\n");
                                cuckoo->fails += 1;
                        }
                }
                ctx->stage = CUCKOO_FIND_STAGE_CALCHASH;
                break;
        }

        return done;
}

/*
 *
 */
always_inline unsigned
init_find_engine(struct cuckoo_find_engine_s *engine,
                 unsigned nb,
                 struct cuckoo_node_s **node_pp,
                 const void * const *key_pp,
                 unsigned ctx_nb)
{
        unsigned alives = 0;
        engine->node_nb = 0;

        if (nb) {
                engine->node_pp = node_pp;
                engine->key_pp = key_pp;
                engine->next = 0;
                engine->req_nb = nb;

                engine->ctx_pool_size = CUCKOO_PIPELIN_STAGE_NB * ctx_nb;

                for (unsigned i = 0; i < engine->ctx_pool_size; i++) {
                        struct cuckoo_find_ctx_s *ctx = &engine->ctx_pool[i];

                        ctx->idx   = CUCKOO_INVALID_IDX;
                        ctx->stage = CUCKOO_FIND_STAGE_CALCHASH - (i % CUCKOO_PIPELIN_STAGE_NB);
                        ctx->found = NULL;

                        alives |= (1 << i);
                }
        }
        return alives;
}

/*
 *
 */
always_inline unsigned
find_engine(struct cuckoo_hash_s *cuckoo,
            struct cuckoo_node_s **node_pp,
            const void * const *key_pp,
            unsigned nb)
{
        struct cuckoo_find_engine_s *engine = &cuckoo->engine;
        unsigned alives;

        set_debug_handler(cuckoo);

        uint64_t tsc = rdtsc();
        idx_pool_next_prefetch(cuckoo, 1);

        alives = init_find_engine(engine, nb, node_pp, key_pp, cuckoo->ctx_nb);

        while (alives) {
                for (unsigned i = 0; alives && (i < engine->ctx_pool_size); i++) {
                        unsigned mask = (1 << i);
                        if (alives & mask) {
                                if (do_find_ctx(cuckoo, engine, nb, &engine->ctx_pool[i]))
                                        alives &= ~mask;
                        }
                }
        }

        cuckoo->tsc += (rdtsc() - tsc);
        cuckoo->cnt += nb;

        cls_debug_handler(cuckoo);

        return engine->node_nb;
}

/***************************************************************************************************
 * API
 ***************************************************************************************************/
/*
 *
 */
union cuckoo_hash_u
cuckoo_calc_hash(const struct cuckoo_hash_s *cuckoo,
                 const void *key)
{
        return cuckoo->calc_hash(key, cuckoo->key_len, idx_tbl_mask(&cuckoo->bk_tbl));
}

/*
 *
 */
unsigned
cuckoo_find_bulk(struct cuckoo_hash_s *cuckoo,
                 const void * const *key_pp,
                 unsigned nb,
                 struct cuckoo_node_s **node_pp)
{
        return find_engine(cuckoo, node_pp, key_pp, nb);
}

static size_t
node_tbl_sizeof(unsigned nb,
                unsigned key_len)
{
        size_t size;

#if defined(KEY_IS_IN_BUCKET)
        size = sizeof(struct cuckoo_node_s);
        (void) key_len;
#else
        size = sizeof(struct cuckoo_node_s) + key_len;
#endif
        size *= nb;
        size = CEIL_MULTIPLE(size, CUCKOO_CACHELINE_SIZE);
        return size;
}

static size_t
bk_tbl_sizeof(unsigned nb,
              unsigned key_len)
{
        size_t size;

#if defined(KEY_IS_IN_BUCKET)
        size = sizeof(struct cuckoo_bucket_s) + (key_len * CUCKOO_BUCKET_ENTRY_SZ);
#else
        size = sizeof(struct cuckoo_bucket_s);
        (void) key_len;
#endif

        nb = nb_nodes(nb);
        nb = nb_buckets(nb);

        size *= nb;
        size = CEIL_MULTIPLE(size, CUCKOO_CACHELINE_SIZE);

        return size;
}



/*
 *
 */
size_t
cuckoo_sizeof(unsigned nb,
              unsigned key_len)
{
        size_t sz = sizeof(struct cuckoo_hash_s);
        unsigned node_size;
        unsigned bk_size;

#if defined(KEY_IS_IN_BUCKET)
        node_size = sizeof(struct cuckoo_node_s);
        bk_size = sizeof(struct cuckoo_bucket_s) + (key_len * CUCKOO_BUCKET_ENTRY_SZ);
#else
        node_size = sizeof(struct cuckoo_node_s) + key_len;
        bk_size = sizeof(struct cuckoo_bucket_s);
#endif
        node_size = CEIL_MULTIPLE(node_size, CUCKOO_CACHELINE_SIZE);
        bk_size = CEIL_MULTIPLE(bk_size, CUCKOO_CACHELINE_SIZE);

        nb = nb_nodes(nb);

        sz += idx_pool_sizeof(nb, CUCKOO_CACHELINE_SIZE);
        sz += bk_size * nb_buckets(nb);
        sz += node_size * nb;

        TRACER("nb:%u sz:%zu\n", nb, sz);
        return sz;
}

/*
 *
 */
int
cuckoo_init(struct cuckoo_hash_s *cuckoo,
            unsigned nb,
            unsigned key_len,
            unsigned ctx_nb,
            cuckoo_hash_func_t calc_hash,
            cuckoo_user_initializer_t user_init,
            void *user_array,
            unsigned user_len,
            unsigned flags)
{
        TRACER("cuckoo:%p nb:%u ctx:%u key_len:%u flags:%x user_array:%p user_len:%u\n",
               cuckoo, nb, ctx_nb, key_len, flags, user_array, user_len);

        if (key_len % sizeof(uint64_t) || !key_len)
                return -1;

        /* set user data array */
        if (!user_init || !user_array || !user_len)
                return -1;
        cuckoo->user_init = user_init;

        if (!ctx_nb)
                ctx_nb = 1;

        unsigned node_nb = nb_nodes(nb);
        unsigned bucket_nb = nb_buckets(node_nb);
        unsigned node_size;
        unsigned bk_size;

#if defined(KEY_IS_IN_BUCKET)
        node_size = sizeof(struct cuckoo_node_s);
        bk_size = sizeof(struct cuckoo_bucket_s) + (key_len * CUCKOO_BUCKET_ENTRY_SZ);
#else
        node_size = sizeof(struct cuckoo_node_s) + key_len;
        bk_size = sizeof(struct cuckoo_bucket_s);
#endif
        node_size = CEIL_MULTIPLE(node_size, 16);
        bk_size = CEIL_MULTIPLE(bk_size, CUCKOO_CACHELINE_SIZE);

        TRACER("re-size node:%u bucket:%u\n", node_nb, bucket_nb);

        cuckoo->cnt = 0;
        cuckoo->tsc = 0;
        cuckoo->fails = 0;
        cuckoo->opt_flags = flags;
        cuckoo->key_len = key_len;
        memset(cuckoo->bkcnt, 0, sizeof(cuckoo->bkcnt));

        if ((ctx_nb * CUCKOO_PIPELIN_STAGE_NB) > ARRAYOF(cuckoo->engine.ctx_pool))
                cuckoo->ctx_nb = ARRAYOF(cuckoo->engine.ctx_pool) / CUCKOO_PIPELIN_STAGE_NB;
        else
                cuckoo->ctx_nb = ctx_nb;

        cuckoo->find_idx  = GENERIC_find_idx_in_bucket;
        cuckoo->find_hval = GENERIC_find_hval_in_bucket;
        cuckoo->calc_hash = GENERIC_calc_hash;

#if defined(__x86_64__)
        x86_handler_init(cuckoo, flags);
#elif defined(__ARM_NEON__)
        arm_handler_init(cuckoo, 0);
#endif

        if (calc_hash)
                cuckoo->calc_hash = calc_hash;

        size_t sz = 0;

        {
                /* 1st idx pool */
                idx_pool_init(&cuckoo->idx_pool, nb, &cuckoo->payload[sz]);
                sz += idx_pool_sizeof(node_nb, CUCKOO_CACHELINE_SIZE);
        }

        {
                /* 2nd bucket */
                struct cuckoo_bucket_s *bk = (struct cuckoo_bucket_s *) &cuckoo->payload[sz];
                size_t size = bk_tbl_sizeof(nb, key_len);

                memset(bk, -1, size);
                idx_tbl_init(&cuckoo->bk_tbl, bk_size, bucket_nb - 1, bk);

                sz += size;
        }

        {
                /* 3rd node */
                struct cuckoo_node_s *node = (struct cuckoo_node_s *) &cuckoo->payload[sz];
                size_t size = node_tbl_sizeof(nb, key_len);

                memset(node, -1, size);
                idx_tbl_init(&cuckoo->node_tbl, node_size, node_nb - 1, node);
                idx_tbl_init(&cuckoo->user_tbl, user_len, node_nb - 1, user_array);

                IDXQ_INIT(&cuckoo->used_fifo, node);
        }

        return 0;
}

/*
 *
 */
void
cuckoo_reset(struct cuckoo_hash_s *cuckoo)
{
        cuckoo->cnt = 0;
        cuckoo->tsc = 0;
        cuckoo->fails = 0;
        cuckoo->bkcnt[0] = 0;
        cuckoo->bkcnt[1] = 0;
        cuckoo->bkcnt[2] = 0;

        struct idx_pool_s *pool = &cuckoo->idx_pool;

        idx_pool_init(pool, pool->nb_idx, pool->idx_array);
        IDXQ_INIT(&cuckoo->used_fifo, node_ptr(cuckoo, 0));

        for (unsigned i = 0; i < pool->nb_idx; i++) {
                struct cuckoo_node_s *node = node_ptr(cuckoo, i);
                memset(node, -1, sizeof(*node));
        }

        for (unsigned i = 0; i < idx_tbl_nb(&cuckoo->bk_tbl); i++) {
                struct cuckoo_bucket_s *bk = bucket_ptr(cuckoo, i);
                memset(bk, -1, sizeof(*bk));
        }
}

/*
 *
 */
struct cuckoo_hash_s *
cuckoo_create(unsigned nb,
              unsigned key_len,
              unsigned ctx_nb,
              cuckoo_hash_func_t calc_hash,
              cuckoo_user_initializer_t user_init,
              void *user_array,
              unsigned user_len,
              unsigned flags)
{
        TRACER("nb:%u calc_hash:%p user_init:%p\n", nb, calc_hash, user_init);

        struct cuckoo_hash_s *cuckoo = aligned_alloc(CUCKOO_CACHELINE_SIZE, cuckoo_sizeof(nb, key_len));

        if (cuckoo) {
                if (cuckoo_init(cuckoo, nb, key_len, ctx_nb, calc_hash,
                                user_init, user_array, user_len,
                                flags)) {
                        free(cuckoo);
                        cuckoo = NULL;
                }
        }

        TRACER("cuckoo:%p\n", cuckoo);
        return cuckoo;
}

/*
 *
 */
unsigned
cuckoo_max_node(const struct cuckoo_hash_s *cuckoo)
{
        return idx_pool_nb(&cuckoo->idx_pool);
}

/*
 *
 */
unsigned
cuckoo_used_num(const struct cuckoo_hash_s *cuckoo)
{
        return idx_pool_used(&cuckoo->idx_pool);
}

/*
 *
 */
unsigned
cuckoo_empty_num(const struct cuckoo_hash_s *cuckoo)
{
        return idx_pool_nb(&cuckoo->idx_pool) - idx_pool_used(&cuckoo->idx_pool);
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
                {
                        struct cuckoo_node_s *node;

                        node = IDXQ_PREV(&cuckoo->used_fifo, ctx->node, entry);
                        if (node)
                                prefetch(node, 3);
                        node = IDXQ_NEXT(&cuckoo->used_fifo, ctx->node, entry);
                        if (node)
                                prefetch(node, 3);
                }

                /* for prefetch, not used */
                fetch_bucket(cuckoo, hash2idx(cuckoo, ctx->node->hash, 0));
                //fetch_bucket(cuckoo, hash2idx(cuckoo, ctx->node->hash, 1));

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
                        idx_pool_free(&cuckoo->idx_pool, node_idx(cuckoo, ctx->node));
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
        const void *key_p;
        union cuckoo_hash_u *hash_p;
        unsigned idx;
        enum cuckoo_hash_state_e state;
};

/*
 *
 */
struct cuckoo_hash_engine_s {
        struct cuckoo_hash_ctx_s ctx_pool[28];

        cuckoo_hash_func_t calc_hash;
        const void * const *key_pp;
        union cuckoo_hash_u *hash_p;
        unsigned key_len;
        unsigned mask;
        unsigned next;
};

/*
 *
 */
always_inline void
init_hash_engine(struct cuckoo_hash_engine_s *engine,
                 cuckoo_hash_func_t hash_func,
                 const void * const *key_pp,
                 union cuckoo_hash_u *hash_p,
                 unsigned mask,
                 unsigned key_len)
{
        engine->calc_hash = hash_func;
        engine->key_pp = key_pp;
        engine->hash_p = hash_p;
        engine->key_len = key_len;
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
                        ctx->hash_p = &engine->hash_p[ctx->idx];
                        prefetch(ctx->key_p, 3);
                        ctx->state = CUCKOO_HASH_STATE_CALC;
                } else {
                        ctx->state = CUCKOO_HASH_STATE_DONE;
                }
                break;

        case CUCKOO_HASH_STATE_CALC:
                *(ctx->hash_p) = engine->calc_hash(ctx->key_p, engine->key_len, engine->mask);
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
                 const void * const *key_pp,
                 union cuckoo_hash_u *hash_p,
                 unsigned nb)
{
        struct cuckoo_hash_engine_s engine;

        init_hash_engine(&engine, cuckoo->calc_hash, key_pp, hash_p, idx_tbl_mask(&cuckoo->bk_tbl),
                         cuckoo->key_len);
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
                FILE *stream,
                const char *title,
                const void *key)
{
        char msg[256];
        unsigned len;
        union cuckoo_hash_u hash = cuckoo_calc_hash(cuckoo, key);
        const uint8_t *p = key;

        len = snprintf(msg, sizeof(msg), "%s hval:%08x key:\n", title, hash2val(hash));
        for (unsigned i = 0; i < cuckoo->key_len; i++) {
                len += snprintf(&msg[len], sizeof(msg) - len, "%02x ", p[i]);
                if ((i + 1) % 16 == 0) {
                        fprintf(stream, "%s\n", msg);
                        len = 0;
                }
        }
        if (len)
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
        fprintf(stream, "%s node:%u hash:%08x %08x\n",
                title, node_idx(cuckoo, node),
                node->hash.val32[0],
                node->hash.val32[1]);
#if !defined(KEY_IS_IN_BUCKET)
        cuckoo_key_dump(cuckoo, stream, "in node", &node->key);
#endif
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

#if defined(KEY_IS_IN_BUCKET)
        for (unsigned pos = 0; pos < ARRAYOF(bk->key); pos++) {
                char msg[256];

                snprintf(msg, sizeof(msg), "bk:%u pos:%2u", bucket_idx(cuckoo, bk), pos);
                cuckoo_key_dump(cuckoo, stream, msg, &bk->key[pos]);
        }
#endif
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
                "%s cuckoo:%p ctx_nb:%u key_len:%u flags:%x "
                "fails:%"PRIu64" cnt:%"PRIu64" %0.2f bk0:%"PRIu64" bk1:%"PRIu64" bkf:%"PRIu64"\n",
                title,
                cuckoo,
                cuckoo->ctx_nb,
                cuckoo->key_len,
                cuckoo->opt_flags,
                cuckoo->fails,
                cnt,
                (double) tsc / cnt,
                cuckoo->bkcnt[0], cuckoo->bkcnt[1], cuckoo->bkcnt[2]);

        idx_pool_dump(&cuckoo->idx_pool, stream, "idx pool");
        idx_tbl_dump(&cuckoo->node_tbl, stream, "node tbl");
        idx_tbl_dump(&cuckoo->bk_tbl, stream, "bk tbl");
        idx_tbl_dump(&cuckoo->user_tbl, stream, "user tbl");
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
                idx = (idx ^ hash2val(node->hash)) & idx_tbl_mask(&cuckoo->bk_tbl);
                bk = bucket_ptr(cuckoo, idx);
        }
        return bk;
}

/*
 *
 */
const void *
cuckoo_key(const struct cuckoo_hash_s *cuckoo,
           const struct cuckoo_node_s *node)
{
#if defined(KEY_IS_IN_BUCKET)
        unsigned pos = -1;
        struct cuckoo_bucket_s *bk = fetch_cuckoo_current_bucket(cuckoo, node, &pos);
        if (bk)
                return &bk->key[pos][0];
#else
        (void) cuckoo;
        return &node->key[0];
#endif
        return NULL;
}

/*
 *
 */
int
cuckoo_verify(const struct cuckoo_hash_s *cuckoo,
              const struct cuckoo_node_s *node,
              const void *key)
{
        int ret = -1;
        uint32_t idx = node_idx(cuckoo, node);
        char msg[256];

        if (!node) {
                fprintf(stderr, "node is NULL\n");
                goto end;
        }

        struct cuckoo_bucket_s *cur_bk, *ano_bk;
        unsigned pos = -1;

        cur_bk = fetch_cuckoo_current_bucket(cuckoo, node, &pos);
        if (!cur_bk) {
                fprintf(stderr, "unknown current bucket. node:%u\n", idx);
                goto end;
        }

        const void *k = GET_KEY(cuckoo, cur_bk, pos);

        if (cmp_key(cuckoo, k, key)) {
                snprintf(msg, sizeof(msg), "node:%u current:%u pos:%u",
                         node_idx(cuckoo,node), bucket_idx(cuckoo, cur_bk), pos);
                cuckoo_key_dump(cuckoo, stderr, msg, k);
                cuckoo_key_dump(cuckoo, stderr, "key", key);
                fprintf(stderr, "mismatched key. node:%u\n", idx);
                goto end;
        }

        ano_bk = fetch_cuckoo_another_bucket(cuckoo, cur_bk, pos);
        if (!ano_bk) {
                fprintf(stderr, "unknown another bucket. node:%u\n", idx);
                goto end;
        }

        union cuckoo_hash_u hash = cuckoo_calc_hash(cuckoo, key);
        if (node->hash.val64 != hash.val64) {
                fprintf(stderr, "mismatched hash. node:%u\n", idx);
                goto end;
        }

        if (((hash2val(hash) ^ bucket_idx(cuckoo, ano_bk)) & idx_tbl_mask(&cuckoo->bk_tbl)) !=
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
/*
 * 48 + 8 bytes
 */
union test_key_u {
        uint8_t data[48];
        uint32_t d32[12];
        uint64_t d64[6 ];
};

static void
speed_test_hash_bulk(struct cuckoo_hash_s *cuckoo,
                     union test_key_u **key_pp,
                     unsigned nb)
{
        uint64_t tsc;
        union cuckoo_hash_u hash[nb];

        cuckoo->calc_hash = GENERIC_calc_hash;
        tsc = rdtsc();
        cuckoo_hash_bulk(cuckoo, (const void * const *) key_pp, hash, nb);
        tsc = rdtsc() - tsc;
        fprintf(stdout, "Generic bulk hash speed %0.2f tsc/key\n", (double) tsc / nb);

        cuckoo->calc_hash = SSE42_calc_hash;
        tsc = rdtsc();
        cuckoo_hash_bulk(cuckoo, (const void * const *) key_pp, hash, nb);
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
        struct cuckoo_hash_s cuckoo _CUCKOO_CACHE_ALIGNED;
        uint32_t idx[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_bucket_s bk[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_node_s node[CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        struct cuckoo_find_ctx_s ctx [CUCKOO_BUCKET_ENTRY_SZ] _CUCKOO_CACHE_ALIGNED;
        uint64_t hits[1024];
};

static void
unit_test(void)
{
        struct test_s *tbl = aligned_alloc(CUCKOO_CACHELINE_SIZE, sizeof(*tbl));
        if (tbl) {
                memset(tbl, 0, sizeof(*tbl));

                struct cuckoo_hash_s *cuckoo = &tbl->cuckoo;
                unsigned key_len = 0;
#if defined(KEY_IS_IN_BUCKET)
                unsigned node_size = sizeof(struct cuckoo_node_s);
                unsigned bk_size = sizeof(struct cuckoo_bucket_s) + (key_len * CUCKOO_BUCKET_ENTRY_SZ);
#else
                unsigned node_size = sizeof(struct cuckoo_node_s) + key_len;
                unsigned bk_size = sizeof(struct cuckoo_bucket_s);
#endif


                idx_pool_init(&cuckoo->idx_pool, ARRAYOF(tbl->idx), tbl->idx);
                idx_tbl_init(&cuckoo->bk_tbl, bk_size, ARRAYOF(tbl->bk) - 1, tbl->bk);
                idx_tbl_init(&cuckoo->node_tbl, node_size, ARRAYOF(tbl->node) - 1, tbl->node);

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

                uint64_t tsc;
                unsigned cnt = 0;

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

                free(tbl);
        }
}

static const uint32_t HVAL[] = {
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
};

static union cuckoo_hash_u
test_hash(const void *key,
          unsigned key_len,
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

static union test_key_u **
init_key(unsigned nb)
{
        size_t sz = sizeof(union test_key_u *) + sizeof(union test_key_u);

        union test_key_u ** array_p = calloc(nb, sz);
        union test_key_u * array = (union test_key_u *) &array_p[nb];
        for (unsigned i = 0; i < nb; i++)
                array_p[i] = &array[i];

        for (unsigned i = 0; i < ARRAYOF(array->d32); i++) {
                random_key(array_p, nb);
                for (unsigned j = 0; j < nb; j++)
                        array_p[j]->d32[i] = random();
        }
        random_key(array_p, nb);

        return array_p;
}

static union cuckoo_hash_u
same_hash(const void *key,
          unsigned key_len,
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
        fprintf(stdout, "\n%s start %u\n\n", __func__, nb);

        cuckoo_hash_func_t calk_hash = test_hash;

        SWAP(cuckoo->calc_hash, calk_hash);

        fprintf(stdout, "\nADD\n");
        struct cuckoo_node_s *node = cuckoo_find_oneshot(cuckoo, key);

        if (node) {
                struct cuckoo_bucket_s *bk_0, *bk_1;

                cuckoo_node_dump(cuckoo, stdout, "ADD ok", node);
                cuckoo_key_dump(cuckoo, stdout, "ADD ok", key);

                bk_0 = cuckoo_current_bucket(cuckoo, node);
                bk_1 = cuckoo_another_bucket(cuckoo, node);

                cuckoo_bucket_dump(cuckoo, stdout, "ADD ok current", bk_0);
                cuckoo_bucket_dump(cuckoo, stdout, "ADD ok another", bk_1);
                cuckoo_dump(cuckoo, stdout, "ADD ok");

                if (cuckoo_verify(cuckoo, node, key)) {
                        fprintf(stdout, "verify failed on add\n");
                        goto end;
                }

                if (cuckoo_flipflop(cuckoo, node)) {
                        fprintf(stdout, "FlipFlop ng\n");
                        goto end;
                } else {
                        fprintf(stdout, "FlipFlop ok\n");
                        if (cuckoo_verify(cuckoo, node, key)) {
                                fprintf(stdout, "verify failed on FlipFlop\n");
                                goto end;
                        }
                }

                bk_0 = cuckoo_current_bucket(cuckoo, node);
                bk_1 = cuckoo_another_bucket(cuckoo, node);

                cuckoo_node_dump(cuckoo, stdout, "After FlipFlop", node);
                cuckoo_bucket_dump(cuckoo, stdout, "After FlipFlop current", bk_0);
                cuckoo_bucket_dump(cuckoo, stdout, "After FlipFlop another", bk_1);
                cuckoo_dump(cuckoo, stdout, "After FlipFlop");

                struct cuckoo_node_s *found = cuckoo_find_oneshot(cuckoo, key);
                if (node != found) {
                        fprintf(stderr, "mismatched node.");
                        goto end;
                }

                cuckoo_del_oneshot(cuckoo, node);
                cuckoo_node_dump(cuckoo, stdout, "After free", node);
                cuckoo_bucket_dump(cuckoo, stdout, "After free current", bk_1);
                cuckoo_bucket_dump(cuckoo, stdout, "After free another", bk_0);
                cuckoo_dump(cuckoo, stdout, "After free Cache");

                ret = 0;
        } else {
                fprintf(stdout, "ADD ng\n");
        }

 end:
        fprintf(stdout, "\n");
        dump_all(cuckoo);
        fprintf(stdout, "\n%s end %d\n\n", __func__, ret);
        SWAP(cuckoo->calc_hash, calk_hash);
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
        fprintf(stdout, "\n%s start %u\n", __func__, nb);

        int ret = -1;
        struct cuckoo_node_s *node[CUCKOO_BUCKET_ENTRY_SZ + 1];
        struct cuckoo_bucket_s *bk[2];
        cuckoo_hash_func_t calk_hash = same_hash;

        cuckoo_reset(cuckoo);
        SWAP(cuckoo->calc_hash, calk_hash);

        node[0] = cuckoo_find_oneshot(cuckoo, key[0]);
        bk[0] = cuckoo_current_bucket(cuckoo, node[0]);
        bk[1] = cuckoo_another_bucket(cuckoo, node[0]);

        for (unsigned i = 1; i < ARRAYOF(node); i++) {
                char title[80];

                snprintf(title, sizeof(title), "%u th", i);
                node[i] = cuckoo_find_oneshot(cuckoo, key[i]);
                if (!node[i]) {
                        char msg[80];
                        snprintf(msg, sizeof(msg), "not found node %u", i);

                        cuckoo_key_dump(cuckoo, stdout, msg, key[i]);
                        dump_all(cuckoo);
                        goto end;
                }
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
        fprintf(stdout, "%s ret:%d\n\n", __func__, ret);
        SWAP(cuckoo->calc_hash, calk_hash);
        return ret;
}


struct verify_s {
        union test_key_u **key_pp;
        unsigned idx;
};

static int
verify_cb(struct cuckoo_hash_s *cuckoo,
          struct cuckoo_node_s *node,
          void *arg)
{
        struct verify_s *verify = arg;

        const union test_key_u *key = cuckoo_key(cuckoo, node);
        if (memcmp(key, verify->key_pp[verify->idx], cuckoo->key_len)) {
                fprintf(stderr, "%s:%d mismatched key %u\n",
                        __func__, __LINE__, verify->idx);
                return -1;
        }
        fprintf(stderr, "%s:%d Ok %u\n", __func__, __LINE__, verify->idx);

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
                fprintf(stderr, "Bad walk\n");
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
max_test(struct cuckoo_hash_s *cuckoo,
         union test_key_u **key_pp,
         unsigned nb)
{
        fprintf(stdout, "\n%s start %u\n", __func__, nb);

        int ret = -1;
        struct cuckoo_node_s **node = calloc(idx_tbl_nb(&cuckoo->node_tbl), sizeof(*node));
        struct cuckoo_node_s **n2 = calloc(idx_tbl_nb(&cuckoo->node_tbl), sizeof(*n2));

        cuckoo_reset(cuckoo);
        cuckoo->cnt = 0;
        cuckoo->tsc = 0;

        /* bulk without hash */
        unsigned n = cuckoo_find_bulk(cuckoo,
                                      (const void * const *) key_pp,
                                      nb, node);
        unsigned count = 0;
        for (unsigned i = 0; i < nb; i++) {
                if (node[i]) {
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
                fprintf(stdout, "Error\n");
                goto end;
        }

        if (count != cuckoo_used_num(cuckoo)) {
                fprintf(stdout, "Bulk(w) unmatched num: n=%u nb=%u count=%u\n",
                       n, cuckoo_used_num(cuckoo), count);
                goto end;
        }

        unsigned m = cuckoo_find_bulk(cuckoo, (const void * const *) key_pp,
                                      nb, n2);
        if (n != m) {
                fprintf(stdout, "mismatched found keys m:%u n:%u\n", m, n);
                goto end;
        }
        for (unsigned i = 0; i < nb; i++) {
                if (node[i] != n2[i]) {
                        fprintf(stdout, "mismatched node %u\n", i);
                        goto end;
                }
        }

        fprintf(stdout, "start free\n");
        random_node(node, idx_tbl_nb(&cuckoo->node_tbl));
        uint64_t tsc = rdtsc();
        unsigned del_nb = cuckoo_del_bulk(cuckoo, node, idx_tbl_nb(&cuckoo->node_tbl));
        if (del_nb != m) {
                fprintf(stdout, "mismatched deleted m:%u del:%u\n", m, del_nb);
                goto end;
        }
        fprintf(stdout, "delete %0.2f tsc/del\n", (double) (rdtsc() - tsc) / del_nb);

        ret = 0;
 end:
        cuckoo_dump(cuckoo, stdout, "Last dump");
        fprintf(stdout, "%s:%d ret:%d\n\n", __func__, __LINE__, ret);
        free(node);
        free(n2);
        return ret;
}

static double
speed_sub_sub(struct cuckoo_hash_s *cuckoo,
              union test_key_u **key_pp,
              unsigned nb)
{
        union test_key_u key[256];
        struct cuckoo_node_s *node[256];
        union test_key_u *key_p[256];
        double tsc = 0;

        for (unsigned k = 0; k < ARRAYOF(key); k++)
                key_p[k] = &key[k];

        uint64_t start_cnt = cuckoo->cnt;
        uint64_t start_tsc = cuckoo->tsc;
        for (unsigned base = 0; base < nb; base += ARRAYOF(key)) {
                unsigned num;

                for (unsigned k = 0; k < ARRAYOF(key); k++)
                        copy_key(cuckoo, &key[k], key_pp[base + k]);

                num = cuckoo_find_bulk(cuckoo, (const void * const *) key_p,
                                       ARRAYOF(key), node);
                if (ARRAYOF(key) != num) {
                        fprintf(stdout, "xxx Failure. num:%u base:%u\n", num, base);
                        goto end;
                }
        }
        tsc = (double) (cuckoo->tsc - start_tsc) / (cuckoo->cnt - start_cnt);
 end:
         return tsc;
}

static int
speed_sub(struct cuckoo_hash_s *cuckoo,
          union test_key_u **key_pp,
          unsigned nb)
{
        double add = 0, search = 0;
        unsigned target_num = 256 * 1;
        cuckoo_reset(cuckoo);

#if defined(ENABLE_PAPI)
        int ret = PAPI_library_init(PAPI_VER_CURRENT);
        if (ret < 0) {
                fprintf(stderr, "Failed to init PAPI lib. %s\n",
                        PAPI_strerror(ret));
                return -1;
        }
        int EventSet = PAPI_NULL;
        int events[] = { PAPI_TLB_DM, PAPI_TOT_INS, PAPI_TOT_CYC, };

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
                add += speed_sub_sub(cuckoo, key_pp, nb);

                random_key(key_pp, nb);
                cuckoo->tsc = 0;
                cuckoo->cnt = 0;
                search += speed_sub_sub(cuckoo, key_pp, target_num);
        }

#if defined(ENABLE_PAPI)
        long long values[4];
        ret = PAPI_stop(EventSet, values);
        if (ret != PAPI_OK) {
                fprintf(stderr, "Failed to stop PAPI event set. %s\n",
                        PAPI_strerror(ret));
                return -1;
        }
        PAPI_shutdown();
        fprintf(stdout, "IPC:%0.2f %lld\n",
                (double) values[1] / values[2],
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
        cuckoo->opt_flags &= ~CUCKOO_DISABLE_FLAG(CUCKOO_DISABLE_LIST);

        for (unsigned i = 0; i < 2; i++) {
                uint64_t best_tsc = UINT64_C(-1);
                unsigned best_nb = -1;

                for (unsigned ctx_nb = 1; ctx_nb < 9; ctx_nb++) {
                        cuckoo->ctx_nb = ctx_nb;
                        cuckoo_reset(cuckoo);

                        random_key(key_pp, nb);
                        speed_sub_sub(cuckoo, key_pp, nb);

                        random_key(key_pp, nb);
                        speed_sub_sub(cuckoo, key_pp, nb);

                        if (best_tsc > cuckoo->tsc) {
                                best_tsc = cuckoo->tsc;
                                best_nb = ctx_nb;
                        }
                        fprintf(stdout, "ctx_nb:%u flags:%x\n",
                                best_nb, cuckoo->opt_flags);
                }
                cuckoo->opt_flags |= CUCKOO_DISABLE_FLAG(CUCKOO_DISABLE_LIST);
        }
}

static int
speed_test(struct cuckoo_hash_s *cuckoo,
           union test_key_u **key_pp,
           unsigned nb)
{
       int ret = -1;

       nb = cuckoo_max_node(cuckoo);
       nb &= ~255;

       fprintf(stdout, "\n%s start %u\n", __func__, nb);
       if (!nb)
               goto end;

       for (unsigned i = 0; i < 10; i++) {
               ret = speed_sub(cuckoo, key_pp, nb);
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
measure_cache_clear(unsigned nb_lines)
{
        struct cacheline_s *lines = aligned_alloc(CACHELINE_SIZE, sizeof(*lines) * nb_lines);
        int ret = -1;
        if (lines) {
                for (unsigned i = 0; i < nb_lines; i++)
                        lines[i].val[0] = i;
                ret = 0;
                free(lines);
        }
        return ret;
}

static int
measure_latency(unsigned nb_lines)
{
        struct cacheline_s *lines = aligned_alloc(CACHELINE_SIZE, sizeof(*lines) * nb_lines);
        int ret = -1;

        if (lines) {
                unsigned index[256];
                double total_cycles = 0.0;

                for (unsigned i = 0; i < nb_lines; i++) {
                        lines[i].val[0] = i;
                }

                if (measure_cache_clear(262144 * 1.5))
                        goto end;

                for (unsigned i = 0; i < ARRAYOF(index); i++)
                        index[i] = rand() % nb_lines;

                total_cycles += measure_chunk(lines, index, ARRAYOF(index));

                printf("Average cache miss latency: nb:%u %f cycles\n",
                       nb_lines,
                       total_cycles / ARRAYOF(index));
                ret = 0;
        end:
                free(lines);
        }
        return ret;
}

static void
measure_cache_miss_latency_tsc(void)
{
        unsigned nb_lines = 262144;
        int ret;

        do {
                ret = measure_latency(nb_lines);
                nb_lines <<= 1;
        } while (!ret);
}

/***************************************************************************************************
 *
 ***************************************************************************************************/
static int
idx_test(struct cuckoo_hash_s *cuckoo)
{
        struct cuckoo_node_s *node;
        struct idx_tbl_s node_idx_tbl;

        fprintf(stderr, "%s:%d start\n", __func__, __LINE__);

        idx_tbl_init(&node_idx_tbl, sizeof(*node) + cuckoo->key_len, -1, cuckoo->node_tbl.base);

        for (unsigned idx = 0; idx < idx_tbl_nb(&cuckoo->node_tbl); idx++) {
                node = idx2ptr(&node_idx_tbl, idx);

                if (node_ptr(cuckoo, idx) != node) {
                        fprintf(stderr, "failed idx2ptr idx:%u\n", idx);
                        return -1;
                }

                if (ptr2idx(&node_idx_tbl, node) != node_idx(cuckoo, node)) {
                        fprintf(stderr, "failed ptr2idx idx:%u\n", idx);
                        return -1;
                }
        }
        fprintf(stderr, "%s:%d success\n", __func__, __LINE__);
        return 0;
}

#define PAGE_SIZE	 1024 * 1024 * 1024
static void *
alloc_hugepage(size_t *len)
{
        size_t size;
        for (size = PAGE_SIZE; size < *len; size += PAGE_SIZE)
                ;
        void *p = mmap(NULL, size,
                       PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB,
                       -1, 0);
        if (p == MAP_FAILED) {
                perror("mmap");
                return NULL;
        }

        memset(p, 0, size);

        *len = size;
        return p;
}

static void
free_hugepage(void *p,
              size_t len)
{
        if (munmap(p, len) == -1) {
                fprintf(stderr, "failed to munmap\n");
                perror("munmap");
        }
}

static int
user_data_init(void *user_data __attribute__((unused)),
               unsigned user_len __attribute__((unused)),
               const void *key __attribute__((unused)),
               unsigned key_len __attribute__((unused)))
{
        return 0;
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
            unsigned flags)
{
        struct cuckoo_hash_s *cuckoo;
        uint64_t *user_array = malloc(sizeof(*user_array) * nb);

        size_t len = cuckoo_sizeof(nb, sizeof(union test_key_u));

        fprintf(stdout, "nb:%u size:%zu %fMB\n", nb, len, (double) len/1024/1024);

        if (do_hp)
                cuckoo = alloc_hugepage(&len);
        else
                cuckoo = aligned_alloc(CUCKOO_CACHELINE_SIZE, len);

        cuckoo_init(cuckoo, nb, sizeof(union test_key_u), ctx_size, NULL,
                    user_data_init, user_array, sizeof(*user_array),
                    flags);
        cuckoo_dump(cuckoo, stdout, "Root");

        if (idx_test(cuckoo))
                goto end;

        union test_key_u **key = init_key(nb);

        if (do_basic) {
                if (single_add_del_test(cuckoo, key, nb))
                        goto end;

                if (collision_test(cuckoo, key, nb))
                        goto end;

                if (max_test(cuckoo, key, nb))
                        goto end;
        }

        if (do_speed_test) {
                if (speed_test(cuckoo, key, nb))
                        goto end;
        }

        if (do_analyze)
                analyze_ctx_num(cuckoo, key, nb);

        if (do_unit) {
                speed_test_hash_bulk(cuckoo, key, nb);
                unit_test();
        }


 end:
        if (do_hp)
                free_hugepage(cuckoo, len);
        else
                free(cuckoo);

        if (do_mem)
                measure_cache_miss_latency_tsc();
        return 0;
}

#endif /* ENABLE_UINIT_TEST */
