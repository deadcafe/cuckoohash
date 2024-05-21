#ifndef _TINYALLOCATOR_H_
#define _TINYALLOCATOR_H_

#include <sys/types.h>
#include <stdbool.h>

struct mem_root_s;

extern struct mem_root_s *TMA_create(size_t total_size,
                                     size_t block_size,
                                     bool use_hugepage);

extern void TMA_destroy(struct mem_root_s *root);

extern void *TMA_alloc(struct mem_root_s *root,
                       size_t len);

extern void TMA_free(struct mem_root_s *root,
                     void *ptr);

#endif	/* !_TINYALLOCATOR_H_ */
