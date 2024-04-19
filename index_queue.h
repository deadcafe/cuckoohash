/* SPDX-License-Identifier: BSD-2-Clause
 * Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
 */

#ifndef _INDEX_QUEUE_H_
#define _INDEX_QUEUE_H_
/*
 * Index Tail queue definitions.
 * Note: array[0] element is Reserved.
 */
#define _IDXQ_HEAD(name, type, qual) \
struct name { \
    qual type *idxq_base; /* array top */ \
    unsigned idxq_first; /* first element index */ \
    unsigned idxq_last; /* index of last element */ \
}
#define IDXQ_HEAD(name, type) _IDXQ_HEAD(name, struct type,)

#define IDXQ_NULL (unsigned) -1
#define IDXQ_P2IDX(head, elm) ((elm) == NULL ? IDXQ_NULL : ((elm) - (head)->idxq_base))
#define IDXQ_IDX2P(head, idx) ((idx) == IDXQ_NULL ? NULL : (&((head)->idxq_base[(idx)])))

#define _IDXQ_ENTRY(type, qual) \
struct idxq_entry { \
    unsigned idxq_next; /* next element */ \
    unsigned idxq_prev; /* previous element */ \
}
#define IDXQ_ENTRY(type) _IDXQ_ENTRY(struct type,)

/*
 * Tail queue access methods.
 */
#define IDXQ_EMPTY(head) ((head)->idxq_first == IDXQ_NULL)
#define IDXQ_VALID(head, idx) ((idx) != IDXQ_NULL)

#define IDXQ_FIRST(head) IDXQ_IDX2P((head), (head)->idxq_first)
#define IDXQ_LAST(head) IDXQ_IDX2P((head), (head)->idxq_last)

#define IDXQ_NEXT(head, elm, field) IDXQ_IDX2P((head), ((elm)->field.idxq_next))
#define IDXQ_PREV(head, elm, field) IDXQ_IDX2P((head), ((elm)->field.idxq_prev))

/*
 * Tail queue functions.
 */
#define IDXQ_INIT(head, tbl) do { \
    (head)->idxq_base = (tbl); \
    (head)->idxq_first = IDXQ_NULL; \
    (head)->idxq_last = IDXQ_NULL; \
} while (0)

#define IDXQ_INSERT_HEAD(head, elm, field) do { \
    unsigned idx = IDXQ_P2IDX((head), (elm)); \
    if ((head)->idxq_first == IDXQ_NULL) \
        (head)->idxq_last = idx; \
    else \
        (head)->idxq_base[(head)->idxq_first].field.idxq_prev = idx; \
    (elm)->field.idxq_next = (head)->idxq_first; \
    (elm)->field.idxq_prev = IDXQ_NULL; \
    (head)->idxq_first = idx; \
} while (0)

#define IDXQ_INSERT_TAIL(head, elm, field) do { \
    unsigned idx = IDXQ_P2IDX((head), (elm)); \
    if ((head)->idxq_last == IDXQ_NULL) \
        (head)->idxq_first = idx; \
    else \
        (head)->idxq_base[(head)->idxq_last].field.idxq_next = idx; \
    (elm)->field.idxq_next = IDXQ_NULL; \
    (elm)->field.idxq_prev = (head)->idxq_last; \
    (head)->idxq_last = idx; \
} while (0)

#define IDXQ_REMOVE(head, elm, field) do { \
    if ((elm)->field.idxq_prev != IDXQ_NULL) \
        (head)->idxq_base[(elm)->field.idxq_prev].field.idxq_next = (elm)->field.idxq_next; \
    else \
        (head)->idxq_first = (elm)->field.idxq_next; \
    if ((elm)->field.idxq_next != IDXQ_NULL) \
        (head)->idxq_base[(elm)->field.idxq_next].field.idxq_prev = (elm)->field.idxq_prev; \
    else \
        (head)->idxq_last = (elm)->field.idxq_prev; \
} while (0)

#define IDXQ_FOREACH(var, head, field) \
    for ((var) = IDXQ_FIRST((head)); \
         (var) != NULL; \
         (var) = IDXQ_NEXT((head), (var), field))

#define IDXQ_FOREACH_REVERSE(var, head, field) \
    for ((var) = IDXQ_LAST((head)); \
         (var) != NULL; \
         (var) = IDXQ_PREV((head), (var), field))

#define IDXQ_FOREACH_SAFE(var, head, field, next) \
    for ((var) = IDXQ_FIRST((head)), \
        (next) = (var) ? IDXQ_NEXT((head), (var), field) : NULL; \
        (var) != NULL; \
        (var) = (next), (next) = (var) ? IDXQ_NEXT((head), (var), field) : NULL)

#define IDXQ_FOREACH_REVERSE_SAFE(var, head, field, next) \
    for ((var) = IDXQ_LAST((head)), \
        (next) = (var) ? IDXQ_PREV((head), (var), field) : NULL; \
        (var) != NULL; \
        (var) = (next), (next) = (var) ? IDXQ_PREV((head), (var), field) : NULL)

#define IDXQ_PUSH(head, elm, field) \
    IDXQ_INSERT_HEAD(head, elm, field)

#define IDXQ_POP(head, elm, field) do { \
    elm = IDXQ_FIRST(head); \
    if (elm) IDXQ_REMOVE(head, elm, field); \
} while (0)

#define IDXQ_ENQUEUE(head, elm, field) \
    IDXQ_INSERT_TAIL(head, elm, field)

#define IDXQ_DEQUEUE(head, elm, field) do { \
    elm = IDXQ_FIRST(head); \
    if (elm) IDXQ_REMOVE(head, elm, field); \
} while (0)

#endif /* _INDEX_QUEUE_H_ */
