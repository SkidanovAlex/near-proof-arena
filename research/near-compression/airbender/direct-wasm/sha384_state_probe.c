/* Measurement adapter only: intermediate SHA384 chaining states for already
 * padded messages. Not a prover/verifier primitive and no proof claim. */
#include <openssl/sha.h>
#include <stddef.h>
#include <stdint.h>
int near_sha384_states(const unsigned char *padded, size_t length,
                       uint64_t *states, size_t capacity) {
    if (!padded || !states || !length || length % 128 || length > (1u << 24)) return 1;
    size_t blocks = length / 128;
    if (capacity < 8 * (blocks + 1)) return 2;
    SHA512_CTX ctx;
    if (!SHA384_Init(&ctx)) return 3;
    for (size_t j = 0; j < 8; ++j) states[j] = (uint64_t)ctx.h[j];
    for (size_t i = 0; i < blocks; ++i) {
        SHA512_Transform(&ctx, padded + 128*i);
        for (size_t j = 0; j < 8; ++j) states[8*(i+1)+j] = (uint64_t)ctx.h[j];
    }
    return 0;
}
