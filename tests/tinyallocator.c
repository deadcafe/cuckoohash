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
#include <sys/types.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "tinyallocator.h"

/***************************************************************************************************
 * Hugepage memory allocator
 ***************************************************************************************************/
struct mem_chunk_s {
        void *mem;

        unsigned start_bit;
        unsigned width;
        TAILQ_ENTRY(mem_chunk_s) entry;
};

TAILQ_HEAD(mem_chunk_list_s, mem_chunk_s);

struct mem_root_s {
        void *mem;
        size_t total_size;
        size_t block_size;

        struct mem_chunk_list_s used_head;
        struct mem_chunk_list_s free_head;

        size_t bitmap_nb;
        size_t total_bits;

        struct mem_chunk_s chunks[64];
        uint64_t bitmap[0] __attribute__((aligned(64)));
};

#define BITS_PER_WORD (sizeof(uint64_t) * 8)
#define SET_BIT(arr, idx) (arr[(idx) / BITS_PER_WORD] |= (UINT64_C(1) << ((idx) % BITS_PER_WORD)))
#define CLEAR_BIT(arr, idx) (arr[(idx) / BITS_PER_WORD] &= ~(UINT64_C(1) << ((idx) % BITS_PER_WORD)))
#define IS_BIT_SET(arr, idx) (arr[(idx) / BITS_PER_WORD] & (UINT64_C(1) << ((idx) % BITS_PER_WORD)))

#ifndef ARRAYOF
# define ARRAYOF(_a)     (sizeof(_a)/sizeof(_a[0]))
#endif

#ifndef SWAP
# define SWAP(a,b) do { typeof(a) _c = (a); (a) = (b); (b) = _c;} while (0)
#endif

#ifndef CEIL_MULTIPLE
# define CEIL_MULTIPLE(value, multiple) (((value) + (multiple) - 1) / (multiple) * (multiple))
#endif


static int
find_head(uint64_t *bitmap,
          size_t total_bits,
          size_t width)
{
        ssize_t best_start = -1;
        size_t best_length = 0;
        ssize_t start = -1;
        size_t length = 0;
#if 0
        fprintf(stderr, "%s:%d bitmap:%p total:%zu width:%zu\n",
                __func__, __LINE__, bitmap, total_bits, width);
#endif

        for (size_t i = 0; i < total_bits; ++i) {
#if 0
                fprintf(stderr, "%s:%d i:%zu val:%"PRIx64" start:%zd length:%zu\n",
                                __func__, __LINE__,
                        i, bitmap[i / BITS_PER_WORD],
                        start, length);
#endif

                if (!IS_BIT_SET(bitmap, i)) {
                        if (start == -1) {
                                start = (ssize_t) i;
                        }
                        length++;
                } else {
                        // ビットが埋まっている場合
                        if (length >= width &&
                            (length > best_length || best_length == 0)) {
                                best_start = start;
                                best_length = length;
                        }
                        start = -1;
                        length = 0;
                }
        }

        // 終了時に連続する空き領域があれば最適な値を設定
        if (length >= width &&
            (length > best_length || best_length == 0)) {
                best_start = start;
        }

        //        fprintf(stderr, "best_start:%zd\n", best_start);
        return best_start == -1 ? -1 : (int) best_start;
}

void *
TMA_alloc(struct mem_root_s *root,
          size_t len)
{
        size_t width;
        int start_bit;

        //        fprintf(stderr, "%s:%d len:%zu\n", __func__, __LINE__, len);

        len = CEIL_MULTIPLE(len, root->block_size);
        width = len / root->block_size;
        start_bit = find_head(root->bitmap, root->total_bits, width);

        //        fprintf(stderr, "%s:%d width:%zu start=%d\n", __func__, __LINE__, width, start_bit);

        if (start_bit >= 0) {
                struct mem_chunk_s *chunk = TAILQ_FIRST(&root->free_head);
                if (chunk) {
                        TAILQ_REMOVE(&root->free_head, chunk, entry);

                        chunk->width = (unsigned) width;
                        chunk->start_bit = (unsigned) start_bit;

                        chunk->mem = ((char *) (root->mem)) + ((unsigned) start_bit * root->block_size);
                        memset(chunk->mem, 0, len);

                        for (unsigned  i = 0; i < width; i++)
                                SET_BIT(root->bitmap, i + (unsigned) start_bit);

                        TAILQ_INSERT_TAIL(&root->used_head, chunk, entry);

                        //                        fprintf(stderr, "%s:%d mem:%p\n", __func__, __LINE__, chunk->mem);
                        return chunk->mem;
                }
        }
        fprintf(stderr, "%s:%d not enough memory %zu\n", __func__, __LINE__, len);
        exit(0);
        return NULL;
}

void
TMA_free(struct mem_root_s *root,
         void *mem)
{
        //        fprintf(stderr, "%s:%d mem:%p\n", __func__, __LINE__, mem);
        if (mem) {
                struct mem_chunk_s *chunk;

                TAILQ_FOREACH(chunk, &root->used_head, entry) {
                        if (chunk->mem == mem) {
                                break;
                        }
                }

                if (chunk) {
                        TAILQ_REMOVE(&root->used_head, chunk, entry);
                        TAILQ_INSERT_TAIL(&root->free_head, chunk, entry);

                        for (unsigned  i = 0; i < chunk->width; i++)
                                CLEAR_BIT(root->bitmap, i + chunk->start_bit);
                } else {
                        fprintf(stderr, "%s:%d invalid pointer %p\n", __func__, __LINE__, mem);
                        exit(0);
                }
        }
}

void
TMA_destroy(struct mem_root_s *root)
{
        if (root) {
                if (root->mem != MAP_FAILED) {
                        if (munmap(root->mem, root->total_size) == -1)
                                perror("munmap:");
                        free(root);
                }
        }
}

/*
 * Tiny Memory Allocator
 */
struct mem_root_s *
TMA_create(size_t total_size,
           size_t block_size,
           bool use_hugepage)
{
        size_t total_bits;
        size_t bitmap_nb;
        struct mem_root_s *root;

        total_size = CEIL_MULTIPLE(total_size, block_size);
        total_bits = total_size / block_size;
        bitmap_nb = total_bits / BITS_PER_WORD;

        root = calloc(1, sizeof(*root) + (sizeof(uint64_t) * bitmap_nb));
        if (root) {
                int flags =  MAP_PRIVATE | MAP_ANONYMOUS;

                if (use_hugepage)
                        flags |= MAP_HUGETLB;

                root->mem = mmap(NULL, total_size,
                                 PROT_READ | PROT_WRITE,
                                 flags,
                                 -1, 0);

                if (root->mem == MAP_FAILED) {
                        perror("mmap:");
                        TMA_destroy(root);
                        root = NULL;
                } else {
                        fprintf(stdout, "%s:%d total size:%zu block size:%zu nb:%zu bits:%zu mmap:%p\n",
                                __func__, __LINE__,
                                total_size, block_size, bitmap_nb, total_bits, root->mem);

                        root->total_size = total_size;
                        root->block_size = block_size;
                        root->bitmap_nb = bitmap_nb;
                        root->total_bits = total_bits;

                        TAILQ_INIT(&root->used_head);
                        TAILQ_INIT(&root->free_head);

                        for (unsigned i = 0; i < ARRAYOF(root->chunks); i++)
                                TAILQ_INSERT_TAIL(&root->free_head, &root->chunks[i], entry);
                }
        }
        return root;
}

