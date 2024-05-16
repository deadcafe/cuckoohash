#ifndef _XXHASH_H_
#define _XXHASH_H_

#include <sys/types.h>
#include <stdint.h>

extern uint64_t XXH3_hash64(const void *input, size_t len, uint64_t seed);

#endif	/* !_XXHASH_H_ */
