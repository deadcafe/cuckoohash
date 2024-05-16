

/*
 * xxHash - Extremely Fast Hash algorithm
 * Copyright (C) 2012-2021 Yann Collet
 *
 * BSD 2-Clause License (https://www.opensource.org/licenses/bsd-license.php)
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *    * Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.
 *    * Redistributions in binary form must reproduce the above
 *      copyright notice, this list of conditions and the following disclaimer
 *      in the documentation and/or other materials provided with the
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
 *
 * You can contact the author at:
 *   - xxHash homepage: https://www.xxhash.com
 *   - xxHash source repository: https://github.com/Cyan4973/xxHash
 */

#include <stddef.h>
#include <assert.h>
#include <stdint.h>
#include <stdalign.h>

#include "xxhash.h"

#define XXH_PRIME64_1  0x9E3779B185EBCA87ULL  /*!< 0b1001111000110111011110011011000110000101111010111100101010000111 */
#define XXH_PRIME64_2  0xC2B2AE3D27D4EB4FULL  /*!< 0b1100001010110010101011100011110100100111110101001110101101001111 */
#define XXH_PRIME64_3  0x165667B19E3779F9ULL  /*!< 0b0001011001010110011001111011000110011110001101110111100111111001 */
#define XXH_PRIME64_4  0x85EBCA77C2B2AE63ULL  /*!< 0b1000010111101011110010100111011111000010101100101010111001100011 */
#define XXH_PRIME64_5  0x27D4EB2F165667C5ULL  /*!< 0b0010011111010100111010110010111100010110010101100110011111000101 */

#define XXH3_MIDSIZE_MAX 240
#define XXH_SECRET_DEFAULT_SIZE 192
#define XXH3_SECRET_SIZE_MIN 136

typedef struct {
        uint64_t low64;   /*!< `value & 0xFFFFFFFFFFFFFFFF` */
        uint64_t high64;  /*!< `value >> 64` */
} XXH128_hash_t;

#define XXH_ALIGN(n)      alignas(n)

XXH_ALIGN(64) static const uint8_t XXH3_kSecret[XXH_SECRET_DEFAULT_SIZE] = {
        0xb8, 0xfe, 0x6c, 0x39, 0x23, 0xa4, 0x4b, 0xbe, 0x7c, 0x01, 0x81, 0x2c, 0xf7, 0x21, 0xad, 0x1c,
        0xde, 0xd4, 0x6d, 0xe9, 0x83, 0x90, 0x97, 0xdb, 0x72, 0x40, 0xa4, 0xa4, 0xb7, 0xb3, 0x67, 0x1f,
        0xcb, 0x79, 0xe6, 0x4e, 0xcc, 0xc0, 0xe5, 0x78, 0x82, 0x5a, 0xd0, 0x7d, 0xcc, 0xff, 0x72, 0x21,
        0xb8, 0x08, 0x46, 0x74, 0xf7, 0x43, 0x24, 0x8e, 0xe0, 0x35, 0x90, 0xe6, 0x81, 0x3a, 0x26, 0x4c,
        0x3c, 0x28, 0x52, 0xbb, 0x91, 0xc3, 0x00, 0xcb, 0x88, 0xd0, 0x65, 0x8b, 0x1b, 0x53, 0x2e, 0xa3,
        0x71, 0x64, 0x48, 0x97, 0xa2, 0x0d, 0xf9, 0x4e, 0x38, 0x19, 0xef, 0x46, 0xa9, 0xde, 0xac, 0xd8,
        0xa8, 0xfa, 0x76, 0x3f, 0xe3, 0x9c, 0x34, 0x3f, 0xf9, 0xdc, 0xbb, 0xc7, 0xc7, 0x0b, 0x4f, 0x1d,
        0x8a, 0x51, 0xe0, 0x4b, 0xcd, 0xb4, 0x59, 0x31, 0xc8, 0x9f, 0x7e, 0xc9, 0xd9, 0x78, 0x73, 0x64,
        0xea, 0xc5, 0xac, 0x83, 0x34, 0xd3, 0xeb, 0xc3, 0xc5, 0x81, 0xa0, 0xff, 0xfa, 0x13, 0x63, 0xeb,
        0x17, 0x0d, 0xdd, 0x51, 0xb7, 0xf0, 0xda, 0x49, 0xd3, 0x16, 0x55, 0x26, 0x29, 0xd4, 0x68, 0x9e,
        0x2b, 0x16, 0xbe, 0x58, 0x7d, 0x47, 0xa1, 0xfc, 0x8f, 0xf8, 0xb8, 0xd1, 0x7a, 0xd0, 0x31, 0xce,
        0x45, 0xcb, 0x3a, 0x8f, 0x95, 0x16, 0x04, 0x28, 0xaf, 0xd7, 0xfb, 0xca, 0xbb, 0x4b, 0x40, 0x7e,
};

static const uint64_t PRIME_MX1 = 0x165667919E3779F9ULL;  /*!< 0b0001011001010110011001111001000110011110001101110111100111111001 */
static const uint64_t PRIME_MX2 = 0x9FB21C651E98DF25ULL;  /*!< 0b1001111110110010000111000110010100011110100110001101111100100101 */


#ifdef __has_builtin
#  define XXH_HAS_BUILTIN(x) __has_builtin(x)
#else
#  define XXH_HAS_BUILTIN(x) 0
#endif

#if XXH_HAS_BUILTIN(__builtin_unreachable)
#  define XXH_UNREACHABLE() __builtin_unreachable()
#else
#  define XXH_UNREACHABLE()
#endif

#define XXH_swap32 __builtin_bswap32
#define XXH_swap64 __builtin_bswap64
#define XXH_likely(x) __builtin_expect(x, 1)
#define XXH_unlikely(x) __builtin_expect(x, 0)

#if !defined(NO_CLANG_BUILTIN) && XXH_HAS_BUILTIN(__builtin_rotateleft32) \
        && XXH_HAS_BUILTIN(__builtin_rotateleft64)
#  define XXH_rotl32 __builtin_rotateleft32
#  define XXH_rotl64 __builtin_rotateleft64
/* Note: although _rotl exists for minGW (GCC under windows), performance seems poor */
#elif defined(_MSC_VER)
#  define XXH_rotl32(x,r) _rotl(x,r)
#  define XXH_rotl64(x,r) _rotl64(x,r)
#else
#  define XXH_rotl32(x,r) (((x) << (r)) | ((x) >> (32 - (r))))
#  define XXH_rotl64(x,r) (((x) << (r)) | ((x) >> (64 - (r))))
#endif

#if XXH_HAS_BUILTIN(__builtin_assume)
#  define XXH_ASSUME(c) __builtin_assume(c)
#else
#  define XXH_ASSUME(c) if (!(c)) { XXH_UNREACHABLE(); }
#endif

#ifndef XXH_HAS_ATTRIBUTE
#  ifdef __has_attribute
#    define XXH_HAS_ATTRIBUTE(...) __has_attribute(__VA_ARGS__)
#  else
#    define XXH_HAS_ATTRIBUTE(...) 0
#  endif
#endif

#if XXH_HAS_ATTRIBUTE(noescape)
# define XXH_NOESCAPE __attribute__((noescape))
#else
# define XXH_NOESCAPE
#endif

#ifndef XXH_DEBUGLEVEL
#  define XXH_DEBUGLEVEL 0
#endif

#if (XXH_DEBUGLEVEL >= 1)
#  include <assert.h>
#  define XXH_ASSERT(c)   assert(c)
#else
#  define XXH_ASSERT(c)   XXH_ASSUME(c)
#endif

#if defined(__LITTLE_ENDIAN__)                                          \
        || (defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
#  define XXH_CPU_LITTLE_ENDIAN 1
#elif defined(__BIG_ENDIAN__)                                           \
        || (defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
#  define XXH_CPU_LITTLE_ENDIAN 0
#endif

#if defined(__GNUC__) || defined(__clang__)
#  define XXH_COMPILER_GUARD(var) __asm__("" : "+r" (var))
#else
#  define XXH_COMPILER_GUARD(var) ((void)0)
#endif

#define XXH_RESTRICT   restrict

#define XXH_FORCE_INLINE static __inline__ __attribute__((always_inline, unused))
#define XXH_NO_INLINE static __attribute__((noinline))
#define XXH_CONSTF  __attribute__((const))
#define XXH_PUREF   __attribute__((pure))
#define XXH_MALLOCF __attribute__((malloc))

static uint32_t
XXH_read32(const void* ptr)
{
        typedef __attribute__((aligned(1))) uint32_t xxh_unalign32;
        return *((const xxh_unalign32*)ptr);
}

XXH_FORCE_INLINE uint32_t
XXH_readLE32(const void* ptr)
{
        return XXH_CPU_LITTLE_ENDIAN ? XXH_read32(ptr) : XXH_swap32(XXH_read32(ptr));
}

static uint64_t
XXH_read64(const void* ptr)
{
        typedef __attribute__((aligned(1))) uint64_t xxh_unalign64;
        return *((const xxh_unalign64*)ptr);
}

XXH_FORCE_INLINE uint64_t
XXH_readLE64(const void* ptr)
{
        return XXH_CPU_LITTLE_ENDIAN ? XXH_read64(ptr) : XXH_swap64(XXH_read64(ptr));
}

XXH_FORCE_INLINE XXH_CONSTF uint64_t
XXH_xorshift64(uint64_t v64,
               int shift)
{
        XXH_ASSERT(0 <= shift && shift < 64);
        return v64 ^ (v64 >> shift);
}

static uint64_t
XXH3_rrmxmx(uint64_t h64,
            uint64_t len)
{
        /* this mix is inspired by Pelle Evensen's rrmxmx */
        h64 ^= XXH_rotl64(h64, 49) ^ XXH_rotl64(h64, 24);
        h64 *= PRIME_MX2;
        h64 ^= (h64 >> 35) + len ;
        h64 *= PRIME_MX2;
        return XXH_xorshift64(h64, 28);
}

static XXH128_hash_t
XXH_mult64to128(uint64_t lhs, uint64_t rhs)
{
        __uint128_t const product = (__uint128_t)lhs * (__uint128_t)rhs;
        XXH128_hash_t r128;
        r128.low64  = (uint64_t)(product);
        r128.high64 = (uint64_t)(product >> 64);
        return r128;
}

static uint64_t
XXH3_mul128_fold64(uint64_t lhs,
                   uint64_t rhs)
{
        XXH128_hash_t product = XXH_mult64to128(lhs, rhs);
        return product.low64 ^ product.high64;
}

static uint64_t
XXH64_avalanche(uint64_t hash)
{
        hash ^= hash >> 33;
        hash *= XXH_PRIME64_2;
        hash ^= hash >> 29;
        hash *= XXH_PRIME64_3;
        hash ^= hash >> 32;
        return hash;
}

XXH_FORCE_INLINE XXH_PUREF uint64_t
XXH3_len_1to3_64b(const uint8_t* input,
                  size_t len,
                  const uint8_t* secret,
                  uint64_t seed)
{
        XXH_ASSERT(input != NULL);
        XXH_ASSERT(1 <= len && len <= 3);
        XXH_ASSERT(secret != NULL);
        /*
         * len = 1: combined = { input[0], 0x01, input[0], input[0] }
         * len = 2: combined = { input[1], 0x02, input[0], input[1] }
         * len = 3: combined = { input[2], 0x03, input[0], input[1] }
         */
        {
                uint8_t  const c1 = input[0];
                uint8_t  const c2 = input[len >> 1];
                uint8_t  const c3 = input[len - 1];
                uint32_t const combined = ((uint32_t)c1 << 16) |
                                          ((uint32_t)c2  << 24) |
                                          ((uint32_t)c3 <<  0) |
                                          ((uint32_t)len << 8);
                uint64_t const bitflip = (XXH_readLE32(secret) ^ XXH_readLE32(secret+4)) + seed;
                uint64_t const keyed = (uint64_t)combined ^ bitflip;
                return XXH64_avalanche(keyed);
        }
}

XXH_FORCE_INLINE XXH_PUREF uint64_t
XXH3_len_4to8_64b(const uint8_t* input,
                  size_t len,
                  const uint8_t* secret,
                  uint64_t seed)
{
        XXH_ASSERT(input != NULL);
        XXH_ASSERT(secret != NULL);
        XXH_ASSERT(4 <= len && len <= 8);
        seed ^= (uint64_t)XXH_swap32((uint32_t)seed) << 32;
        {
                uint32_t const input1 = XXH_readLE32(input);
                uint32_t const input2 = XXH_readLE32(input + len - 4);
                uint64_t const bitflip = (XXH_readLE64(secret+8) ^ XXH_readLE64(secret+16)) - seed;
                uint64_t const input64 = input2 + (((uint64_t)input1) << 32);
                uint64_t const keyed = input64 ^ bitflip;
                return XXH3_rrmxmx(keyed, len);
        }
}

static uint64_t
XXH3_avalanche(uint64_t h64)
{
        h64 = XXH_xorshift64(h64, 37);
        h64 *= PRIME_MX1;
        h64 = XXH_xorshift64(h64, 32);
        return h64;
}

XXH_FORCE_INLINE XXH_PUREF uint64_t
XXH3_len_9to16_64b(const uint8_t* input,
                   size_t len,
                   const uint8_t* secret,
                   uint64_t seed)
{
        XXH_ASSERT(input != NULL);
        XXH_ASSERT(secret != NULL);
        XXH_ASSERT(9 <= len && len <= 16);
        {
                uint64_t const bitflip1 = (XXH_readLE64(secret+24) ^ XXH_readLE64(secret+32)) + seed;
                uint64_t const bitflip2 = (XXH_readLE64(secret+40) ^ XXH_readLE64(secret+48)) - seed;
                uint64_t const input_lo = XXH_readLE64(input)           ^ bitflip1;
                uint64_t const input_hi = XXH_readLE64(input + len - 8) ^ bitflip2;
                uint64_t const acc = len
                                    + XXH_swap64(input_lo) + input_hi
                                    + XXH3_mul128_fold64(input_lo, input_hi);
                return XXH3_avalanche(acc);
        }
}

XXH_FORCE_INLINE XXH_PUREF uint64_t
XXH3_len_0to16_64b(const uint8_t* input,
                   size_t len,
                   const uint8_t* secret,
                   uint64_t seed)
{
        XXH_ASSERT(len <= 16);
        {
                if (XXH_likely(len >  8))
                        return XXH3_len_9to16_64b(input, len, secret, seed);
                if (XXH_likely(len >= 4))
                        return XXH3_len_4to8_64b(input, len, secret, seed);
                if (len)
                        return XXH3_len_1to3_64b(input, len, secret, seed);
                return XXH64_avalanche(seed ^ (XXH_readLE64(secret+56) ^ XXH_readLE64(secret+64)));
        }
}

XXH_FORCE_INLINE uint64_t
XXH3_mix16B(const uint8_t* XXH_RESTRICT input,
            const uint8_t* XXH_RESTRICT secret,
            uint64_t seed64)
{
#if defined(__GNUC__) && !defined(__clang__) /* GCC, not Clang */       \
        && defined(__i386__) && defined(__SSE2__)  /* x86 + SSE2 */     \
        && !defined(XXH_ENABLE_AUTOVECTORIZE)      /* Define to disable like XXH32 hack */
        /*
         * UGLY HACK:
         * GCC for x86 tends to autovectorize the 128-bit multiply, resulting in
         * slower code.
         *
         * By forcing seed64 into a register, we disrupt the cost model and
         * cause it to scalarize. See `XXH32_round()`
         *
         * FIXME: Clang's output is still _much_ faster -- On an AMD Ryzen 3600,
         * XXH3_64bits @ len=240 runs at 4.6 GB/s with Clang 9, but 3.3 GB/s on
         * GCC 9.2, despite both emitting scalar code.
         *
         * GCC generates much better scalar code than Clang for the rest of XXH3,
         * which is why finding a more optimal codepath is an interest.
         */
        XXH_COMPILER_GUARD(seed64);
#endif
        {
                uint64_t const input_lo = XXH_readLE64(input);
                uint64_t const input_hi = XXH_readLE64(input+8);
                return XXH3_mul128_fold64(
                                          input_lo ^ (XXH_readLE64(secret)   + seed64),
                                          input_hi ^ (XXH_readLE64(secret+8) - seed64)
                                          );
        }
}

XXH_FORCE_INLINE XXH_PUREF uint64_t
XXH3_len_17to128_64b(const uint8_t* XXH_RESTRICT input,
                     size_t len,
                     const uint8_t* XXH_RESTRICT secret,
                     size_t secretSize,
                     uint64_t seed)
{
        XXH_ASSERT(secretSize >= XXH3_SECRET_SIZE_MIN); (void)secretSize;
        XXH_ASSERT(16 < len && len <= 128);

        {
                uint64_t acc = len * XXH_PRIME64_1;

                if (len > 32) {
                        if (len > 64) {
                                if (len > 96) {
                                        acc += XXH3_mix16B(input + 48, secret + 96, seed);
                                        acc += XXH3_mix16B(input + len - 64, secret + 112, seed);
                                }
                                acc += XXH3_mix16B(input + 32, secret + 64, seed);
                                acc += XXH3_mix16B(input + len - 48, secret + 80, seed);
                        }
                        acc += XXH3_mix16B(input + 16, secret + 32, seed);
                        acc += XXH3_mix16B(input + len - 32, secret + 48, seed);
                }
                acc += XXH3_mix16B(input + 0, secret + 0, seed);
                acc += XXH3_mix16B(input + len - 16, secret + 16, seed);

                return XXH3_avalanche(acc);
        }
}

#define XXH3_MIDSIZE_MAX 240

XXH_NO_INLINE XXH_PUREF uint64_t
XXH3_len_129to240_64b(const uint8_t* XXH_RESTRICT input,
                      size_t len,
                      const uint8_t* XXH_RESTRICT secret,
                      size_t secretSize,
                      uint64_t seed)
{
        XXH_ASSERT(secretSize >= XXH3_SECRET_SIZE_MIN); (void)secretSize;
        XXH_ASSERT(128 < len && len <= XXH3_MIDSIZE_MAX);

#define XXH3_MIDSIZE_STARTOFFSET 3
#define XXH3_MIDSIZE_LASTOFFSET  17

        {
                uint64_t acc = len * XXH_PRIME64_1;
                uint64_t acc_end;
                unsigned int const nbRounds = (unsigned int)len / 16;
                unsigned int i;
                XXH_ASSERT(128 < len && len <= XXH3_MIDSIZE_MAX);
                for (i = 0; i < 8; i++) {
                        acc += XXH3_mix16B(input + (16 * i), secret + (16 * i), seed);
                }
                /* last bytes */
                acc_end = XXH3_mix16B(input + len - 16,
                                      secret + XXH3_SECRET_SIZE_MIN - XXH3_MIDSIZE_LASTOFFSET, seed);
                XXH_ASSERT(nbRounds >= 8);
                acc = XXH3_avalanche(acc);

#if defined(__clang__)                                /* Clang */       \
        && (defined(__ARM_NEON) || defined(__ARM_NEON__)) /* NEON */    \
        && !defined(XXH_ENABLE_AUTOVECTORIZE)             /* Define to disable */
                /*
                 * UGLY HACK:
                 * Clang for ARMv7-A tries to vectorize this loop, similar to GCC x86.
                 * In everywhere else, it uses scalar code.
                 *
                 * For 64->128-bit multiplies, even if the NEON was 100% optimal, it
                 * would still be slower than UMAAL (see XXH_mult64to128).
                 *
                 * Unfortunately, Clang doesn't handle the long multiplies properly and
                 * converts them to the nonexistent "vmulq_u64" intrinsic, which is then
                 * scalarized into an ugly mess of VMOV.32 instructions.
                 *
                 * This mess is difficult to avoid without turning autovectorization
                 * off completely, but they are usually relatively minor and/or not
                 * worth it to fix.
                 *
                 * This loop is the easiest to fix, as unlike XXH32, this pragma
                 * _actually works_ because it is a loop vectorization instead of an
                 * SLP vectorization.
                 */
#pragma clang loop vectorize(disable)
#endif
                for (i = 8 ; i < nbRounds; i++) {
                        /*
                         * Prevents clang for unrolling the acc loop and interleaving with this one.
                         */
                        XXH_COMPILER_GUARD(acc);
                        acc_end += XXH3_mix16B(input+(16 * i),
                                               secret+(16 * (i - 8)) + XXH3_MIDSIZE_STARTOFFSET, seed);
                }
                return XXH3_avalanche(acc + acc_end);
        }
}

typedef uint64_t (*XXH3_hashLong64_f)(const void* XXH_RESTRICT, size_t,
                                      uint64_t, const uint8_t* XXH_RESTRICT, size_t);

XXH_FORCE_INLINE uint64_t
XXH3_64bits_internal(const void* XXH_RESTRICT input,
                     size_t len,
                     uint64_t seed64,
                     const void* XXH_RESTRICT secret,
                     size_t secretLen,
                     XXH3_hashLong64_f f_hashLong)
{
        XXH_ASSERT(secretLen >= XXH3_SECRET_SIZE_MIN);
        /*
         * If an action is to be taken if `secretLen` condition is not respected,
         * it should be done here.
         * For now, it's a contract pre-condition.
         * Adding a check and a branch here would cost performance at every hash.
         * Also, note that function signature doesn't offer room to return an error.
         */
        if (len <= 16)
                return XXH3_len_0to16_64b((const uint8_t*)input, len,
                                          (const uint8_t*)secret, seed64);
        if (len <= 128)
                return XXH3_len_17to128_64b((const uint8_t*)input, len,
                                            (const uint8_t*)secret, secretLen, seed64);
        if (len <= XXH3_MIDSIZE_MAX)
                return XXH3_len_129to240_64b((const uint8_t*)input, len,
                                             (const uint8_t*)secret, secretLen, seed64);
        return f_hashLong(input, len, seed64, (const uint8_t*)secret, secretLen);
}

static uint64_t
not_supported(const void* input,
              size_t len,
              uint64_t seed64,
              const uint8_t* secret,
              size_t secretLen)
{
        (void)seed64;
        (void)secret; (void)secretLen;
        (void)input; (void)len;

        return UINT64_C(-1);
}

uint64_t
XXH3_hash64(XXH_NOESCAPE const void* input,
            size_t len,
            uint64_t seed)
{
        return XXH3_64bits_internal(input, len,
                                    seed,
                                    XXH3_kSecret, sizeof(XXH3_kSecret),
                                    not_supported);
}
