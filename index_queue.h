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

#ifndef _INDEX_QUEUE_H_
#define _INDEX_QUEUE_H_

/*
 * Index Tail queue definitions.
 * Note: array[0] element is Reserved.
 */
#define _IDXQ_HEAD(name, type, qual)                            \
        struct name {                                           \
                qual type *idxq_base; /* array top */           \
                unsigned idxq_first; /* first element index */  \
                unsigned idxq_last; /* index of last element */ \
}
#define _IDXQ_ENTRY(type, qual)                                 \
        struct idxq_entry {                                     \
                unsigned idxq_next; /* next element */          \
                unsigned idxq_prev; /* previous element */      \
        }
#define IDXQ_HEAD(name, type)   _IDXQ_HEAD(name, struct type,)
#define IDXQ_ENTRY(type)        _IDXQ_ENTRY(struct type,)
#define IDXQ_NULL               ((unsigned) -1)
#define IDXQ_P2IDX(head, elm)   ((elm) == NULL ? IDXQ_NULL : (unsigned) ((elm) - (head)->idxq_base))
#define IDXQ_IDX2P(head, idx)   ((idx) == IDXQ_NULL ? NULL : (&((head)->idxq_base[(idx)])))

/*
 * Tail queue access methods.
 */
#define IDXQ_EMPTY(head)                ((head)->idxq_first == IDXQ_NULL)
#define IDXQ_VALID(head, idx)           ((idx) != IDXQ_NULL)
#define IDXQ_FIRST(head)                IDXQ_IDX2P((head), (head)->idxq_first)
#define IDXQ_LAST(head)                 IDXQ_IDX2P((head), (head)->idxq_last)
#define IDXQ_NEXT(head, elm, field)     IDXQ_IDX2P((head), ((elm)->field.idxq_next))
#define IDXQ_PREV(head, elm, field)     IDXQ_IDX2P((head), ((elm)->field.idxq_prev))

/*
 * Tail queue functions.
 */
#define IDXQ_INIT(head, tbl) do {               \
                (head)->idxq_base = (tbl);      \
                (head)->idxq_first = IDXQ_NULL; \
                (head)->idxq_last = IDXQ_NULL;  \
        } while (0)
#define IDXQ_INSERT_HEAD(head, elm, field) do {                      \
                unsigned _idx = IDXQ_P2IDX((head), (elm));           \
                if ((head)->idxq_first == IDXQ_NULL)                 \
                        (head)->idxq_last = _idx;                    \
                else                                                 \
                        (head)->idxq_base[(head)->idxq_first].field.idxq_prev = _idx; \
                (elm)->field.idxq_next = (head)->idxq_first;         \
                (elm)->field.idxq_prev = IDXQ_NULL;                  \
                (head)->idxq_first = _idx;                           \
        } while (0)
#define IDXQ_INSERT_TAIL(head, elm, field) do {                         \
                unsigned _idx = IDXQ_P2IDX((head), (elm));              \
                if ((head)->idxq_last == IDXQ_NULL)                     \
                        (head)->idxq_first = _idx;                      \
                else                                                    \
                        (head)->idxq_base[(head)->idxq_last].field.idxq_next = _idx; \
                (elm)->field.idxq_next = IDXQ_NULL;                     \
                (elm)->field.idxq_prev = (head)->idxq_last;             \
                (head)->idxq_last = _idx;                               \
        } while (0)
#define IDXQ_REMOVE(head, elm, field) do {                              \
                if ((elm)->field.idxq_prev != IDXQ_NULL)                \
                        (head)->idxq_base[(elm)->field.idxq_prev].field.idxq_next = (elm)->field.idxq_next; \
                else                                                    \
                        (head)->idxq_first = (elm)->field.idxq_next;    \
                if ((elm)->field.idxq_next != IDXQ_NULL)                \
                        (head)->idxq_base[(elm)->field.idxq_next].field.idxq_prev = (elm)->field.idxq_prev; \
                else                                                    \
                        (head)->idxq_last = (elm)->field.idxq_prev;     \
        } while (0)

#define IDXQ_FOREACH(var, head, field)                  \
        for ((var) = IDXQ_FIRST((head));                \
             (var) != NULL;                             \
             (var) = IDXQ_NEXT((head), (var), field))
#define IDXQ_FOREACH_REVERSE(var, head, field)          \
        for ((var) = IDXQ_LAST((head));                 \
             (var) != NULL;                             \
             (var) = IDXQ_PREV((head), (var), field))
#define IDXQ_FOREACH_SAFE(var, head, field, next)                       \
        for ((var) = IDXQ_FIRST((head)),                                \
            (next) = (var) ? IDXQ_NEXT((head), (var), field) : NULL;    \
             (var) != NULL;                                             \
             (var) = (next), (next) = (var) ? IDXQ_NEXT((head), (var), field) : NULL)
#define IDXQ_FOREACH_REVERSE_SAFE(var, head, field, next)               \
        for ((var) = IDXQ_LAST((head)),                                 \
            (next) = (var) ? IDXQ_PREV((head), (var), field) : NULL;    \
             (var) != NULL;                                             \
             (var) = (next), (next) = (var) ? IDXQ_PREV((head), (var), field) : NULL)
#define IDXQ_PUSH(head, elm, field)     IDXQ_INSERT_HEAD(head, elm, field)
#define IDXQ_POP(head, elm, field) do {                 \
                elm = IDXQ_FIRST(head);                 \
                if (elm) IDXQ_REMOVE(head, elm, field); \
        } while (0)
#define IDXQ_ENQUEUE(head, elm, field)  IDXQ_INSERT_TAIL(head, elm, field)
#define IDXQ_DEQUEUE(head, elm, field) do {             \
                elm = IDXQ_FIRST(head);                 \
                if (elm) IDXQ_REMOVE(head, elm, field); \
        } while (0)

/**************************************************************************************
 * index table
 **************************************************************************************/
#define _IDX_TBL(name, type, qual)              \
        struct name {                           \
                qual type *idx_array;           \
                unsigned idx_nb;                \
                unsigned idx_mask;              \
        }
#define IDX_TBL(name, type)	_IDX_TBL(name, struct type,)
#define IDX_TBL_INIT(tbl, array, nb, mask) do {  \
                (tbl)->idx_array = (array);      \
                (tbl)->idx_nb = (nb);            \
                (tbl)->idx_mask = (mask);        \
        } while (0)

#define IDX_TBL_IDX2PTR(tbl, idx)	(idx) == IDXQ_NULL ? NULL : &(tbl)->idx_array[(tbl)->idx_mask & (idx)]
#define IDX_TBL_PTR2IDX(tbl, ptr)	(ptr) == NULL ? IDXQ_NULL : (unsigned) ((ptr) - (tbl)->idx_array)
#define IDX_TBL_LEN(tbl)		sizeof((tbl)->idx_array[0])
#define IDX_TBL_NB(tbl)			((tbl)->idx_nb)
#define IDX_TBL_MASK(tbl)		((tbl)->idx_mask)
#define IDX_TBL_SIZE(tbl)		IDX_TBL_LEN((tbl)) * IDX_TBL_NB((tbl))
#define IDX_TBL_ARRAY(tbl)		((tbl)->idx_array)
#define IDX_TBL_DUMP(tbl, stream, title)                                \
        fprintf((stream), "<%s> tbl:%p array:%p nb:%u mask:%08x\n",     \
                (title), (tbl), (tbl)->idx_array, (tbl)->idx_nb, (tbl)->idx_mask)


#define _IDX_GEN_TBL(name,qual)                 \
        struct name {                           \
                qual uint8_t *idx_array;        \
                unsigned idx_len;               \
                unsigned idx_nb;                \
        }
#define IDX_GEN_TBL(name)	_IDX_GEN_TBL(name,)
#define IDX_GEN_TBL_INIT(tbl, array, len, nb) do {      \
                (tbl)->idx_array = (uint8_t*) (array);  \
                (tbl)->idx_len = (unsigned) (len);      \
                (tbl)->idx_nb = (nb);                   \
        } while (0)
#define IDX_GEN_TBL_DUMP(tbl, stream, title)                            \
        fprintf((stream), "<%s> tbl:%p array:%p len:%u nb:%u\n",        \
                (title), (tbl), (tbl)->idx_array, (tbl)->idx_len, (tbl)->idx_nb)

#define IDX_GEN_TBL_IDX2PTR(tbl, idx)	(idx) == IDXQ_NULL ? NULL : (void*) &(tbl)->idx_array[(idx) * (tbl)->idx_len]
#define IDX_GEN_TBL_PTR2IDX(tbl, ptr)	(ptr) == NULL ? IDXQ_NULL : (unsigned) (((const uint8_t *) (ptr) - (tbl)->idx_array) / (tbl)->idx_len)
#define IDX_GEN_TBL_LEN(tbl)		((tbl)->idx_len)
#define IDX_GEN_TBL_NB(tbl)		((tbl)->idx_nb)
#define IDX_GEN_TBL_ARRAY(tbl)		((tbl)->idx_array)

/**************************************************************************************
 * index pool
 **************************************************************************************/
#define _IDX_POOL(name,qual)                    \
        struct name {                           \
                unsigned idx_nb;                \
                unsigned used_nb;               \
                qual unsigned *idx_array;       \
        }
#define IDX_POOL(name)	_IDX_POOL(name,)
#define IDX_POOL_INIT(pool, array, nb) do {     \
                (pool)->idx_nb = (nb);          \
                (pool)->idx_array = (array);    \
                (pool)->used_nb = 0;            \
                for (unsigned _idx = 0; _idx < (nb); _idx++)    \
                        (pool)->idx_array[_idx] = _idx;         \
        } while (0)
#define IDX_POOL_ALLOC(pool, idx) do {                                  \
                if ((pool)->idx_nb > (pool)->used_nb) {                 \
                        (idx) = (pool)->idx_array[((pool)->used_nb)++]; \
                } else {                                                \
                        (idx) = IDXQ_NULL;                              \
                }                                                       \
        } while (0)
#define IDX_POOL_NEXT(pool, idx) do {                                   \
                if ((pool)->idx_nb > (pool)->used_nb) {                 \
                        (idx) = (pool)->idx_array[(pool)->used_nb + 1]; \
                } else {                                                \
                        (idx) = IDXQ_NULL;                              \
                }                                                       \
        } while (0)
#define IDX_POOL_FREE(pool, idx) do {                                   \
                if ((idx) != IDXQ_NULL)                                 \
                        (pool)->idx_array[--((pool)->used_nb)] = (idx); \
        } while (0)
#define IDX_POOL_NB(pool)	(pool)->idx_nb
#define IDX_POOL_USED(pool)	(pool)->used_nb
#define IDX_POOL_ARRAY(pool)	(pool)->idx_array
#define IDX_POOL_DUMP(pool, stream, title) do {                         \
                fprintf((stream), "<%s> pool:%p nb:%u used:%u array:%p\n", \
                        (title), (pool), (pool)->idx_nb, (pool)->used_nb, (pool)->idx_array); \
        } while (0)

#endif /* _INDEX_QUEUE_H_ */
