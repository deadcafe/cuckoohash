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

#include <sys/queue.h>
#include <sys/mman.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <sched.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <inttypes.h>

#include <xxhash.h>
#include "cuckoohash.h"

#ifndef always_inline
# define always_inline  static inline __attribute__ ((__always_inline__))
#endif  /* !always_inline */

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


#define CUCKOO_FIND_DEPTH	2
#define CUCKOO_PIPELINE_NB	(3 * 9)

#define CUCKOO_COEF			13
#define CUCKOO_EFFECTIVE_CAPA(nb)	(((nb) / CUCKOO_BUCKET_ENTRY_SZ) * CUCKOO_COEF)

#define CUCKOO_INVALID_HASH64	UINT64_C(-1)	/* -1 : invalid */
#define CUCKOO_INVALID_HVAL	IDXQ_NULL
#define CUCKOO_INVALID_IDX	IDXQ_NULL	/* -1 : invalid */
#define CUCKOO_INVALID_FLAGS	UINT64_C(-1)

/***************************************************************************************************
 *
 ***************************************************************************************************/


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
        void **user_pp;

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
        void **user_pp;
        const void * const * key_pp;
        uint32_t *bk_idx;

        unsigned ctx_pool_size;
        unsigned next;
        unsigned req_nb;
        unsigned user_nb;
        bool enable_add;
        bool enable_chain;
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
        IDX_TBL(bk_tbl_s, cuckoo_bucket_s) bk_tbl;
        IDX_GEN_TBL(node_tbl_s) node_tbl;
        IDX_GEN_TBL(user_tbl_s) user_tbl;

        /* drivers */
        cuckoo_hash_func_t calc_hash;
        find_idx_in_bucket_t find_idx;
        find_hval_in_bucket_t find_hval;
        cuckoo_user_initializer_t user_init;

        uint64_t cnt;
        uint64_t tsc;
        uint64_t fails;

        uint64_t bkcnt[3];	/* bucket counter 0:1st 1:2nd 2:full */

        IDX_POOL(idx_pool_x) idx_pool;
        IDXQ_HEAD(cuckoo_node_q_s, cuckoo_node_s) used_fifo;

        struct cuckoo_find_engine_s engine _CUCKOO_CACHE_ALIGNED;

        char payload[] _CUCKOO_CACHE_ALIGNED;
};

#define BUCKET_PTR(ck, idx)	IDX_TBL_IDX2PTR(&(ck)->bk_tbl, (idx))
#define BUCKET_IDX(ck, bk)	IDX_TBL_PTR2IDX(&(ck)->bk_tbl, (bk))

#define NODE_PTR(ck, idx)	IDX_GEN_TBL_IDX2PTR(&(ck)->node_tbl, (idx))
#define NODE_IDX(ck, bk)	IDX_GEN_TBL_PTR2IDX(&(ck)->node_tbl, (bk))

#define USER_PTR(ck, idx)	IDX_GEN_TBL_IDX2PTR(&(ck)->user_tbl, (idx))
#define USER_IDX(ck, bk)	IDX_GEN_TBL_PTR2IDX(&(ck)->user_tbl, (bk))


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
prefetch(const void *p,
         const int locality)
{
        __builtin_prefetch((const void *) p, 0, locality);
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
        return (hash.val32[even_odd] & IDX_TBL_MASK(&cuckoo->bk_tbl));
}


/*
 *
 */
always_inline unsigned
bucket_idx(const struct cuckoo_hash_s *cuckoo,
           const struct cuckoo_bucket_s *bk)
{
        return BUCKET_IDX(cuckoo, bk);
}

/*
 *
 */
always_inline struct cuckoo_bucket_s *
bucket_ptr(const struct cuckoo_hash_s *cuckoo,
           uint32_t idx)
{
        return BUCKET_PTR(cuckoo, idx);
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
        uint32_t idx = ((bucket_idx(cuckoo, bk) ^ hval) & IDX_TBL_MASK(&cuckoo->bk_tbl));

        return fetch_bucket(cuckoo, idx);
}

/*
 *
 */
always_inline uint32_t
node_idx(const struct cuckoo_hash_s *cuckoo,
         const struct cuckoo_node_s *node)
{
        return NODE_IDX(cuckoo, node);
}

/*
 *
 */
always_inline struct cuckoo_node_s *
node_ptr(const struct cuckoo_hash_s *cuckoo,
         uint32_t idx)
{
        return NODE_PTR(cuckoo, idx);
}


/*
 *
 */
always_inline uint32_t
user_idx(const struct cuckoo_hash_s *cuckoo,
         const void *user)
{
        return USER_IDX(cuckoo, user);
}

/*
 *
 */
always_inline void *
user_ptr(const struct cuckoo_hash_s *cuckoo,
         uint32_t idx)
{
        return USER_PTR(cuckoo, idx);
}

/*
 *
 */
always_inline void
idx_pool_next_prefetch(const struct cuckoo_hash_s *cuckoo)
{
        unsigned idx;

        IDX_POOL_NEXT(&cuckoo->idx_pool, idx);
        if (idx != IDXQ_NULL)
                prefetch(node_ptr(cuckoo, idx), 3);
}

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
        int pos = __builtin_ctzll(hits);

        for (hits >>= pos; hits; pos++, hits >>= 1) {
                if (hits & 1) {
                        prefetch(GET_KEY(cuckoo, bk, (unsigned) pos), 3);
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
        uint64_t flags;                                                 \
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
        flags = name##_find_32x16(bk->idx, idx);                        \
        TRACER("flags:%04x\n", flags);                                  \
        return flags;                                                   \
}                                                                       \
static inline uint64_t                                                  \
name##_find_hval_in_bucket(const struct cuckoo_hash_s *cuckoo,   	\
                           const struct cuckoo_bucket_s *bk,     	\
                           uint32_t hval)                        	\
{                                                                       \
        uint64_t flags;                                                 \
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
        flags = name##_find_32x16(bk->hval, hval);                      \
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
static inline union cuckoo_hash_u
XXH3_calc_hash(const void *key,
               size_t len,
               uint32_t mask)
{
        union cuckoo_hash_u hash;

        hash.val64 = XXH3_hash64(key, len, 0);
        while (((hash.val32[1] & mask) == (hash.val32[0] & mask)) ||
               ((hash.val32[0] ^ hash.val32[1]) == CUCKOO_INVALID_HVAL)) {
                uint64_t h;

                h = XXH3_hash64(&hash, sizeof(hash), hash.val64);
                hash.val64 ^= h;
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
cacheline_flush(void * ptr)
{
        _mm_clflushopt(ptr);
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
        int flags = 0;

        for (unsigned i = 0; i < 4; i++) {
                __m128i cmp_result = _mm_cmpeq_epi32(key, hash[i]);
                flags |= _mm_movemask_ps(_mm_castsi128_ps(cmp_result)) << (i * 4);
        }
        return (uint64_t) flags;
}

/*
 *
 */
always_inline uint64_t
SSE41_find_32x16(const uint32_t *array,
                 uint32_t val)
{
        __m128i target[4];
        __m128i key = _mm_set1_epi32((int) val);

        for (unsigned i = 0; i < ARRAYOF(target); i++)
                target[i] = _mm_load_si128((const __m128i *) (const void *) &array[i * 4]);
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

static inline uint32_t
crc32c(const void *p,
       size_t length,
       uint32_t seed)
{
        const uint8_t *data = p;
        uint32_t crc = seed;

        // まず、8バイトアラインメントを確認し、アラインされるまで1バイト単位で処理
        while (length && ((uintptr_t) data & 7)) {
                crc = _mm_crc32_u8(crc, *data++);
                length--;
        }

        // アラインされた状態で8バイト単位で処理
        while (length >= 8) {
                crc = (uint32_t) _mm_crc32_u64(crc, *(const uint64_t *) data);
                data += 8;
                length -= 8;
        }

        // 残りのデータを4バイト、2バイト、1バイトで処理
        if (length >= 4) {
                crc = _mm_crc32_u32(crc, *(const uint32_t *) data);
                data += 4;
                length -= 4;
        }
        if (length >= 2) {
                crc = _mm_crc32_u16(crc, *(const uint16_t *) data);
                data += 2;
                length -= 2;
        }
        while (length--) {
                crc = _mm_crc32_u8(crc, *data++);
        }

        return crc;
}

/*
 *
 */
static inline union cuckoo_hash_u
SSE42_calc_hash(const void *key,
                size_t len,
                uint32_t mask)
{
        union cuckoo_hash_u hash;

        hash.val32[0] = crc32c(key, len, UINT32_C(-1));
        hash.val32[1] = 0xdeadbeef;

        hash.val32[1] = __builtin_bswap32(hash.val32[0]) ^ hash.val32[1];

        do {
                uint32_t h = __builtin_bswap32(hash.val32[1]);

                h = (uint32_t) ~_mm_crc32_u64(h, hash.val64);
                hash.val32[1] = h ^ hash.val32[0];
        } while (((hash.val32[1] & mask) == (hash.val32[0] & mask)) ||
                 ((hash.val32[0] ^ hash.val32[1]) == CUCKOO_INVALID_HVAL));

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
        uint64_t mask_lo = (uint64_t) _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(key, hash_lo)));
        uint64_t mask_hi = (uint64_t) _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(key, hash_hi)));
        return (mask_hi << 8) | mask_lo;
}

/*
 *
 */
always_inline uint64_t
AVX2_find_32x16(const uint32_t *array,
                uint32_t val)
{
        return AVX2_cmp_flag(_mm256_load_si256((const __m256i *) (const void *) &array[0]),
                             _mm256_load_si256((const __m256i *) (const void *) &array[8]),
                             _mm256_set1_epi32((int) val));
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
        __m512i target = _mm512_load_si512((const __m512i *) (const void *) array);
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

const struct cuckoo_find_handler_s cuckoo_find_handlers[] = {
        {
                .find_32x16 = GENERIC_find_32x16,
                .name = "GENERIC_find_32x16",
        },
#if defined(__x86_64__)
#  if defined(__SSE4_1__)
        {
                .find_32x16 = SSE41_find_32x16,
                .name = "SSE41_find_32x16",
        },
#  endif
#  if defined(__AVX2__)
        {
                .find_32x16 = AVX2_find_32x16,
                .name = "AVX2_find_32x16",
        },
#  endif /* __AVX2__ */
#  if defined(__AVX512F__)
        {
                .find_32x16 = AVX512_find_32x16,
                .name = "AVX512_find_32x16",
        },
#  endif /* __AVX512F__ */
#elif defined(__ARM_NEON__)
        {
                .find_32x16 = NEON_find_32x16,
                .name = "NEON_find_32x16",
        },
#endif
        {
                .find_32x16 = NULL,
                .name = NULL,
        },
};

const struct cuckoo_calchash_handler_s cuckoo_calchash_handlers[] = {
        {
                .calc_hash = XXH3_calc_hash,
                .name = "XXH3_calc_hash",
        },
#if defined(__x86_64__)
#  if defined(__SSE4_2__)
        {
                .calc_hash = SSE42_calc_hash,
                .name = "SSE42_calc_hash",
        },
#endif
#endif
        {
                .calc_hash = NULL,
                .name = NULL,
        }
};

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
        uint64_t hits;

        for (int eo = 0; eo < 2; eo++) {
                bk = bucket_ptr(cuckoo, hash2idx(cuckoo, hash, eo));

                hits = cuckoo->find_idx(cuckoo, bk, idx);
                if (hits) {
                        *pos_p = (unsigned) __builtin_ctzll(hits);
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

        return (unsigned) __builtin_popcountll(mask);
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
        unsigned nb_buckets;

        nb_entries = nb_nodes(nb_entries);
        nb_buckets = nb_entries / CUCKOO_BUCKET_ENTRY_SZ;

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
        unsigned dst_pos = (unsigned) -1;
        int ret = -1;

        uint64_t empty = cuckoo->find_hval(cuckoo, dst_bk, CUCKOO_INVALID_HVAL);
        if (empty) {
                dst_pos = (unsigned) __builtin_ctzll(empty);

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
                                pos = (int) i;
                                goto end;
                        }
                }

                for (unsigned i = 0; i < CUCKOO_BUCKET_ENTRY_SZ; i++) {
                        struct cuckoo_bucket_s *ano_bk;

                        ano_bk = fetch_cuckoo_another_bucket(cuckoo, bk, i);
                        if (kickout_node(cuckoo, engine, ano_bk, cnt) < 0)
                                continue;

                        if (!flipflop_bucket(cuckoo, engine, bk, i)) {
                                pos = (int) i;
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
        int pos = -1;

        TRACER("bk:%u key:%p hits:%"PRIx64"\n", bucket_idx(cuckoo, bk), key, hits);

        if (hits) {
                pos = __builtin_ctzll(hits);
                for (hits >>= pos; hits; pos++, hits >>= 1) {
                        if (hits & 1) {
                                const uint8_t *k = GET_KEY(cuckoo, bk, (unsigned) pos);
                                if (!cmp_key(cuckoo, k, key)) {
                                        node = node_ptr(cuckoo, bk->idx[pos]);
                                        *pos_p = (unsigned) pos;
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
        uint64_t empt[2];

        TRACER("bk[0]:%u bk[1]:%u hval:%08x\n",
               bucket_idx(cuckoo, ctx->bk[0]), bucket_idx(cuckoo, ctx->bk[1]),
               hash2val(ctx->hash));

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

        IDX_POOL_ALLOC(&cuckoo->idx_pool, node_idx);
        if (node_idx != CUCKOO_INVALID_IDX) {
                void *user = user_ptr(cuckoo, node_idx);

                if (cuckoo->user_init(user, ctx->key_p)) {
                        /* failed to init user data */
                        IDX_POOL_FREE(&cuckoo->idx_pool, node_idx);

                        TRACER("not inserted node:%u free\n", node_idx);
                        node_idx = CUCKOO_INVALID_IDX;
                } else {
                        uint8_t *key;

                        /* set bucket */
                        bk->hval[pos] = hash2val(ctx->hash);
                        bk->idx[pos] = node_idx;

                        key = GET_KEY(cuckoo, bk, (unsigned) pos);
                        copy_key(cuckoo, key, ctx->key_p);

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
#if 1
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
                        ctx->user_pp = &engine->user_pp[ctx->idx];

                        /* calk hash and fetch bucket */
                        ctx->hash = cuckoo->calc_hash(ctx->key_p, cuckoo->key_len,
                                                      IDX_TBL_MASK(&cuckoo->bk_tbl));

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
                        uint32_t idx;

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

                        if (node) {
                                if (engine->enable_chain)
                                        prefetch_neighbor(cuckoo, ctx, node);
                        } else {
                                if (engine->enable_add) {
                                        node = insert_node(cuckoo, engine, ctx);
                                        if (node)
                                                IDXQ_INSERT_HEAD(&cuckoo->used_fifo, node, entry);
                                        else
                                                cuckoo->fails += 1;
                                }
                        }

                        idx = node_idx(cuckoo, node);
                        *ctx->user_pp = user_ptr(cuckoo, idx);
                        if (idx != IDXQ_NULL)
                                engine->user_nb += 1;
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
                 void **user_pp,
                 const void * const *key_pp,
                 unsigned ctx_nb,
                 bool enable_add,
                 bool enable_chain)
{
        unsigned alives = 0;
        engine->user_nb = 0;

        if (nb) {
                engine->user_pp = user_pp;
                engine->key_pp = key_pp;
                engine->next = 0;
                engine->req_nb = nb;
                engine->enable_add = enable_add;
                engine->enable_chain = enable_chain;

                engine->ctx_pool_size = CUCKOO_PIPELIN_STAGE_NB * ctx_nb;

                for (unsigned i = 0; i < engine->ctx_pool_size; i++) {
                        struct cuckoo_find_ctx_s *ctx = &engine->ctx_pool[i];

                        ctx->idx   = CUCKOO_INVALID_IDX;
                        ctx->found = NULL;
#if 1
                        if (i < ctx_nb)
                                ctx->stage = CUCKOO_FIND_STAGE_CALCHASH;
                        else if (i < ctx_nb * 2)
                                ctx->stage = CUCKOO_FIND_STAGE_CALCHASH - 1;
                        else
                                ctx->stage = CUCKOO_FIND_STAGE_CALCHASH - 2;
#else
                        ctx->stage = CUCKOO_FIND_STAGE_CALCHASH - (i % CUCKOO_PIPELIN_STAGE_NB);
#endif
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
            void **user_pp,
            const void * const *key_pp,
            unsigned nb,
            bool enable_add,
            bool enable_chain)
{
        struct cuckoo_find_engine_s *engine = &cuckoo->engine;
        unsigned alives;
        uint64_t tsc;

        set_debug_handler(cuckoo);

        tsc = rdtsc();
        idx_pool_next_prefetch(cuckoo);

        alives = init_find_engine(engine, nb, user_pp, key_pp, cuckoo->ctx_nb,
                                  enable_add, enable_chain);

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

        return engine->user_nb;
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
        return cuckoo->calc_hash(key, cuckoo->key_len, IDX_TBL_MASK(&cuckoo->bk_tbl));
}

/*
 *
 */
unsigned
cuckoo_find_bulk(struct cuckoo_hash_s *cuckoo,
                 const void * const *key_pp,
                 unsigned nb,
                 void **user_pp,
                 bool enable_add,
                 bool enable_chain)
{
        return find_engine(cuckoo, user_pp, key_pp, nb, enable_add, enable_chain);
}

/*
 *
 */
static size_t
node_tbl_sizeof(unsigned nb,
                unsigned key_len,
                size_t *element_sz)
{
        size_t size;

        size = sizeof(struct cuckoo_node_s) + key_len;
        *element_sz = CEIL_MULTIPLE(size, CUCKOO_CACHELINE_SIZE);

        size = *element_sz * nb;
        return size;
}

/*
 *
 */
static size_t
bk_tbl_sizeof(unsigned nb,
              unsigned key_len,
              size_t *element_sz)
{
        size_t size;

        size = sizeof(struct cuckoo_bucket_s);
        (void) key_len;

        *element_sz = CEIL_MULTIPLE(size, CUCKOO_CACHELINE_SIZE);

        nb = nb_buckets(nb);

        size = *element_sz * nb;
        return size;
}

/*
 *
 */
size_t
cuckoo_sizeof(unsigned nb,
              unsigned key_len)
{
        size_t hd_sz = sizeof(struct cuckoo_hash_s);
        size_t node_sz;
        size_t bk_sz;
        size_t pool_sz;
        size_t sz;
        size_t dummy;

        node_sz = sizeof(struct cuckoo_node_s) + key_len;
        bk_sz = sizeof(struct cuckoo_bucket_s);

        pool_sz = idx_pool_sizeof(nb, CUCKOO_CACHELINE_SIZE);
        bk_sz = bk_tbl_sizeof(nb, key_len, &dummy);
        node_sz = node_tbl_sizeof(nb, key_len, &dummy);

        sz = hd_sz + pool_sz + bk_sz + node_sz;

        fprintf(stderr, "nb:%u key_len:%u size:%zu hd:%zu pool:%zu bk:%zu node:%zu\n",
                nb, key_len, sz, hd_sz, pool_sz, bk_sz, node_sz);
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
        size_t sz;

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
        cuckoo->calc_hash = XXH3_calc_hash;

#if defined(__x86_64__)
        x86_handler_init(cuckoo, flags);
#elif defined(__ARM_NEON__)
        arm_handler_init(cuckoo, 0);
#endif

        if (calc_hash)
                cuckoo->calc_hash = calc_hash;

        sz = 0;

        {
                /* 1st idx pool */
                IDX_POOL_INIT(&cuckoo->idx_pool, (unsigned *) &cuckoo->payload[sz], nb);
                sz += idx_pool_sizeof(nb, CUCKOO_CACHELINE_SIZE);
        }

        {
                /* 2nd bucket */
                struct cuckoo_bucket_s *bk = (struct cuckoo_bucket_s *) &cuckoo->payload[sz];
                size_t bk_size;
                size_t size = bk_tbl_sizeof(nb, key_len, &bk_size);
                unsigned bk_nb = nb_buckets(nb);

                IDX_TBL_INIT(&cuckoo->bk_tbl, bk, bk_nb, bk_nb - 1);
                for (unsigned i = 0; i < IDX_TBL_NB(&cuckoo->bk_tbl); i++) {
                        bk = BUCKET_PTR(cuckoo, i);
                        memset(bk->hval, (int) CUCKOO_INVALID_HVAL, sizeof(bk->hval));
                        memset(bk->idx, (int) CUCKOO_INVALID_IDX, sizeof(bk->idx));
                }

                sz += size;
        }

        {
                /* 3rd node */
                struct cuckoo_node_s *node = (struct cuckoo_node_s *) &cuckoo->payload[sz];
                size_t node_sz;
                size_t size = node_tbl_sizeof(nb, key_len, &node_sz);
                (void) size;

                IDX_GEN_TBL_INIT(&cuckoo->node_tbl, node, node_sz, nb);
                for (unsigned i = 0; i < IDX_GEN_TBL_NB(&cuckoo->node_tbl); i++) {
                        node = node_ptr(cuckoo, i);
                        node->hash.val64 = CUCKOO_INVALID_HASH64;
                }

                IDX_GEN_TBL_INIT(&cuckoo->user_tbl, user_array, user_len, nb);
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
        unsigned *pool_array;
        unsigned pool_nb;

        cuckoo->cnt = 0;
        cuckoo->tsc = 0;
        cuckoo->fails = 0;
        cuckoo->bkcnt[0] = 0;
        cuckoo->bkcnt[1] = 0;
        cuckoo->bkcnt[2] = 0;

        pool_array = IDX_POOL_ARRAY(&cuckoo->idx_pool);
        pool_nb = IDX_POOL_NB(&cuckoo->idx_pool);

        IDX_POOL_INIT(&cuckoo->idx_pool, pool_array, pool_nb);
        IDXQ_INIT(&cuckoo->used_fifo, node_ptr(cuckoo, 0));

        for (unsigned i = 0; i < IDX_GEN_TBL_NB(&cuckoo->node_tbl); i++) {
                struct cuckoo_node_s *node = node_ptr(cuckoo, i);
                node->hash.val64 = CUCKOO_INVALID_HASH64;
        }

        for (unsigned i = 0; i < IDX_TBL_NB(&cuckoo->bk_tbl); i++) {
                struct cuckoo_bucket_s *bk = bucket_ptr(cuckoo, i);
                memset(bk->hval, (int) CUCKOO_INVALID_HVAL, sizeof(bk->hval));
                memset(bk->idx, (int) CUCKOO_INVALID_IDX, sizeof(bk->idx));
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
        struct cuckoo_hash_s *cuckoo;
        TRACER("nb:%u calc_hash:%p user_init:%p\n", nb, calc_hash, user_init);

        cuckoo = aligned_alloc(CUCKOO_CACHELINE_SIZE, cuckoo_sizeof(nb, key_len));
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
        return IDX_POOL_NB(&cuckoo->idx_pool);
}

/*
 *
 */
unsigned
cuckoo_used_num(const struct cuckoo_hash_s *cuckoo)
{
        return IDX_POOL_USED(&cuckoo->idx_pool);
}

/*
 *
 */
unsigned
cuckoo_empty_num(const struct cuckoo_hash_s *cuckoo)
{
        return IDX_POOL_NB(&cuckoo->idx_pool) - IDX_POOL_USED(&cuckoo->idx_pool);
}

/*
 *
 */
static int
walk_default(struct cuckoo_hash_s *cuckoo,
             void *user,
             void *arg)
{
        unsigned *nb_p = arg;
        int ret = 0;
        char title[80];
        struct cuckoo_node_s * node = node_ptr(cuckoo, user_idx(cuckoo, user));

        if (cuckoo_used_num(cuckoo) < *nb_p)
                ret = -1;

        snprintf(title, sizeof(title), "Walk Node %uth", *nb_p);
        cuckoo_node_dump(cuckoo, stdout, title, node);

        return ret;
}

/*
 * tail to head order
 */
int
cuckoo_walk(struct cuckoo_hash_s *cuckoo,
            int (*cb_func)(struct cuckoo_hash_s *, void *, void *),
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
                void *user = user_ptr(cuckoo, node_idx(cuckoo, node));

                ret = cb_func(cuckoo, user, arg);
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
        CUCKOO_DEL_STATE_DONE = 0,

        CUCKOO_DEL_STATE_STANDBY_3rd,
        CUCKOO_DEL_STATE_STANDBY_2th,

        CUCKOO_DEL_STATE_PREFETCH_NODE,
        CUCKOO_DEL_STATE_PREFETCH_BK,
        CUCKOO_DEL_STATE_CLEAN,
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

        void **user_pp;
        unsigned deleted_nb;
        unsigned next;
};

/*
 *
 */
always_inline unsigned
init_del_engine(struct cuckoo_del_engine_s *engine,
                void **user_pp)
{
        unsigned alives = 0;

        engine->user_pp = user_pp;
        engine->deleted_nb = 0;
        engine->next = 0;

        for (unsigned i = 0; i < ARRAYOF(engine->ctx_pool); i++) {
                struct cuckoo_del_ctx_s *ctx = &engine->ctx_pool[i];

                switch (i % 3) {
                case 0:
                        ctx->state = CUCKOO_DEL_STATE_PREFETCH_NODE;
                        break;
                case 1:
                        ctx->state = CUCKOO_DEL_STATE_STANDBY_2th;
                        break;
                case 2:
                        ctx->state = CUCKOO_DEL_STATE_STANDBY_3rd;
                        break;
                }
                alives |= (1 << i);
        }
        return alives;
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
        case CUCKOO_DEL_STATE_STANDBY_3rd:
                if (engine->next < nb)
                        ctx->state = CUCKOO_DEL_STATE_STANDBY_2th;
                else
                        ctx->state = CUCKOO_DEL_STATE_DONE;
                break;

        case CUCKOO_DEL_STATE_STANDBY_2th:
                if (engine->next < nb)
                        ctx->state = CUCKOO_DEL_STATE_PREFETCH_NODE;
                else
                        ctx->state = CUCKOO_DEL_STATE_DONE;
                break;

        case CUCKOO_DEL_STATE_PREFETCH_NODE:
        next_data:
                if (engine->next < nb) {
                        uint32_t idx;

                        ctx->idx = engine->next++;
                        idx = user_idx(cuckoo, engine->user_pp[ctx->idx]);
                        ctx->node = node_ptr(cuckoo, idx);
                        if (!ctx->node)
                                goto next_data;

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
                        unsigned pos = 0;
                        struct cuckoo_bucket_s *bk;

                        bk = fetch_cuckoo_current_bucket(cuckoo, ctx->node, &pos);
                        if (bk) {
                                IDXQ_REMOVE(&cuckoo->used_fifo, ctx->node, entry);
                                ctx->node->hash.val64 = CUCKOO_INVALID_HASH64;

                                bk->idx[pos] = CUCKOO_INVALID_IDX;
                                bk->hval[pos] = CUCKOO_INVALID_HVAL;
                        }
                        IDX_POOL_FREE(&cuckoo->idx_pool, node_idx(cuckoo, ctx->node));
                        engine->deleted_nb += 1;
                        ctx->state = CUCKOO_DEL_STATE_PREFETCH_NODE;
                }
                break;

        case CUCKOO_DEL_STATE_DONE:
        default:
                done = 1;
                break;
        }
        return done;
}

/*
 *
 */
unsigned
cuckoo_del_bulk(struct cuckoo_hash_s *cuckoo,
                void **user_pp,
                unsigned nb)
{
        struct cuckoo_del_engine_s engine _CUCKOO_CACHE_ALIGNED;

        unsigned alives = init_del_engine(&engine, user_pp);
        while (alives) {
                for (unsigned i = 0; alives && (i < ARRAYOF(engine.ctx_pool)); i++) {
                        unsigned mask = (1 << i);
                        if (alives & mask) {
                                if (do_del_ctx(cuckoo, &engine, nb, &engine.ctx_pool[i]))
                                        alives &= ~mask;
                        }
                }
        }

        return engine.deleted_nb;
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

        init_hash_engine(&engine, cuckoo->calc_hash, key_pp, hash_p, IDX_TBL_MASK(&cuckoo->bk_tbl),
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
                unsigned pos = 0;
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

        len = (unsigned) snprintf(msg, sizeof(msg), "%s hval:%08x key:\n", title, hash2val(hash));
        for (unsigned i = 0; i < cuckoo->key_len; i++) {
                len += (unsigned) snprintf(&msg[len], sizeof(msg) - len, "%02x ", p[i]);
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
        cuckoo_key_dump(cuckoo, stream, "in node", &node->key);
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
                (double) (tsc / cnt),
                cuckoo->bkcnt[0], cuckoo->bkcnt[1], cuckoo->bkcnt[2]);

        IDX_POOL_DUMP(&cuckoo->idx_pool, stream, "idx pool");
        IDX_TBL_DUMP(&cuckoo->bk_tbl, stream, "bk tbl");
        IDX_GEN_TBL_DUMP(&cuckoo->node_tbl, stream, "node tbl");
        IDX_GEN_TBL_DUMP(&cuckoo->user_tbl, stream, "user tbl");
}

/*
 *
 */
struct cuckoo_bucket_s *
cuckoo_current_bucket(const struct cuckoo_hash_s *cuckoo,
                      const struct cuckoo_node_s * node)
{
        unsigned pos = 0;
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
                unsigned pos = 0;
                uint32_t idx = bucket_idx(cuckoo, fetch_cuckoo_current_bucket(cuckoo, node, &pos));
                idx = (idx ^ hash2val(node->hash)) & IDX_TBL_MASK(&cuckoo->bk_tbl);
                bk = bucket_ptr(cuckoo, idx);
        }
        return bk;
}

/*
 * Found user data to key.
 */
const void *
cuckoo_key(const struct cuckoo_hash_s *cuckoo,
           const void *user)
{
        uint32_t idx = user_idx(cuckoo, user);
        struct cuckoo_node_s *node = node_ptr(cuckoo, idx);

        return &node->key[0];
}

/*
 *
 */
struct cuckoo_node_s *
cuckoo_node(const struct cuckoo_hash_s *cuckoo,
            const void *user)
{
        uint32_t idx = user_idx(cuckoo, user);
        return node_ptr(cuckoo, idx);
}

/*
 *
 */
int
cuckoo_verify(const struct cuckoo_hash_s *cuckoo,
              const void *user,
              const void *key)
{
        int ret = -1;
        struct cuckoo_node_s * node = cuckoo_node(cuckoo, user);
        unsigned idx = node_idx(cuckoo, node);
        char msg[256];
        struct cuckoo_bucket_s *cur_bk, *ano_bk;
        unsigned pos = 0;
        const void *k;
        union cuckoo_hash_u hash;

        if (!node) {
                fprintf(stderr, "node is NULL\n");
                goto end;
        }

        cur_bk = fetch_cuckoo_current_bucket(cuckoo, node, &pos);
        if (!cur_bk) {
                fprintf(stderr, "unknown current bucket. node:%u\n", idx);
                goto end;
        }

        k = GET_KEY(cuckoo, cur_bk, pos);
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

        hash = cuckoo_calc_hash(cuckoo, key);
        if (node->hash.val64 != hash.val64) {
                fprintf(stderr, "mismatched hash. node:%u\n", idx);
                goto end;
        }

        if (((hash2val(hash) ^ bucket_idx(cuckoo, ano_bk)) & IDX_TBL_MASK(&cuckoo->bk_tbl)) !=
            bucket_idx(cuckoo, cur_bk)) {
                fprintf(stderr, "mismatched bucket index. node:%u\n", idx);
                goto end;
        }

        ret = 0;
 end:
        //        fprintf(stdout, "%s ret:%d\n", __func__, ret);
        return ret;
}

void
cuckoo_calkhash_set(struct cuckoo_hash_s *cuckoo,
                    cuckoo_hash_func_t calc_hash)
{
        cuckoo->calc_hash = calc_hash;
}

cuckoo_hash_func_t
cuckoo_calkhash_get(const struct cuckoo_hash_s *cuckoo)
{
        return cuckoo->calc_hash;
}

void
cuckoo_cnt_get(const struct cuckoo_hash_s *cuckoo,
               uint64_t *cnt,
               uint64_t *tsc)
{
        *cnt = cuckoo->cnt;
        *tsc = cuckoo->tsc;
}

void
cuckoo_ctxnb_set(struct cuckoo_hash_s *cuckoo,
                 unsigned nb)
{
        cuckoo->ctx_nb = nb;
}

unsigned
cuckoo_bucket_idx(const struct cuckoo_hash_s *cuckoo,
                  const struct cuckoo_bucket_s *bk)
{
        return bucket_idx(cuckoo, bk);
}

struct cuckoo_node_s *
cuckoo_node_ptr(const struct cuckoo_hash_s *cuckoo,
                unsigned idx)
{
        return node_ptr(cuckoo, idx);
}

