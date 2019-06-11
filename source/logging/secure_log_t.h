#ifndef __SECURE_LOG_T__
#define __SECURE_LOG_T__

#include "log_t.h"

#define SECURE_LOG_ENTRY_LENGTH 256+sizeof(digest)

typedef log_name secure_log_name;
typedef log secure_log;
typedef log_io_stream secure_log_io_stream;
typedef struct secure_log_entries {
  log_entry the_entry;
  digest the_digest;
} secure_log_entry;
typedef enum { none, hashchain_sha2_256, hashchain_sha3_256 } integrity;
typedef enum { none, aes_cbc, rsa_1024 } provenance;
typedef enum { none, all_plaintext, all_ciphertext } confidentiality;

#endif
