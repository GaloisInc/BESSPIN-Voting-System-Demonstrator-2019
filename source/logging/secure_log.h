/**
 * Smart Ballot Logging API
 * @refine log.lando
 */
#ifndef __SECURE_LOG__
#define __SECURE_LOG__

// General includes

// Subsystem includes
#include "secure_log_t.h"

// @design kiniry We should probably write `the_policy` into the log's
// root block and authenticate it.
secure_log create_secure_log(const secure_log_name the_secure_log_name,
                             const log_entry a_log_entry_type,
                             const secure_log_security_policy the_policy);

secure_log_entry secure_log_entry_kind(const secure_log_name a_secure_log_name);

void write_entry_to_secure_log(const secure_log the_secure_log,
                               const log_entry a_log_entry);

bool verify_secure_log_entry_security(const secure_log_entry the_secure_log_entry);

bool verify_secure_log_security(const secure_log the_secure_log);

#endif /* __SECURE_LOG__ */
