/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes

// Subsystem includes
#include "secure_log.h"
#include "hsm.h"

// Local constants

const aes256_key test_key = { 0 };

// Local functions

// Refines Cryptol initialLogEntry
/*@
    requires \valid_read (key + (0 .. AES256_KEY_LENGTH_BYTES - 1));
    requires \valid_read (msg + (0 .. LOG_ENTRY_LENGTH - 1));
    requires \separated (key, msg);
    assigns \nothing;
*/
static secure_log_entry initial_log_entry(const aes256_key key, // IN
			                  const log_entry msg)  // IN
{
  secure_log_entry initial_entry;

  // 1. Zero-pad msg to exactly 256 chars with zeros.
  // log_entry is exactly 256 chars, so we'll assume this has already been
  // done by the caller.

  // 2. Form "hmac key msg"
  hmac (key, msg, LOG_ENTRY_LENGTH, &initial_entry.the_digest[0]);

  // 3. Copy the msg data
  /*@
      loop invariant 0 <= i <= LOG_ENTRY_LENGTH;
      loop invariant \forall size_t j; 0 <= j < i ==> initial_entry.the_entry[j] == msg[j];
      loop assigns i, initial_entry.the_entry[0 .. LOG_ENTRY_LENGTH - 1];
      loop variant LOG_ENTRY_LENGTH - i;
  */
  for (size_t i = 0; i < LOG_ENTRY_LENGTH; i++)
    {
      initial_entry.the_entry[i] = msg[i];
    }

  return initial_entry; // struct by copy return
}


// Exported functions

void create_secure_log(Log_Handle *secure_log,
                       const secure_log_name the_secure_log_name,
                       const log_entry a_log_entry_type,
                       const secure_log_security_policy the_policy)
{
  Log_FS_Result create_result, write_result, sync_result;
  secure_log_entry initial_entry;
  
  // Initial/Draft pseudo-code by RCC

  // 1. Create new file, open for writing only.
  create_result = Log_IO_Create_New (secure_log, the_secure_log_name);
  
  // 2. call initial_log_entry above to create the first block
  initial_entry = initial_log_entry (test_key, a_log_entry_type);
  
  // 3. Write that new block to the file.
  write_result = Log_IO_Write_Entry (secure_log, initial_entry);
  
  // 4. sync the file.
  sync_result = Log_IO_Sync (secure_log);
  
  // TBDs - what about error cases?
  //   What if the file already exists? Perhaps a pre-condition here that it doesn't
  //    already exist, so up to the caller to spot that and do the right thing...
  //    We may have to implement an f_exists() API (and ACSL logic function) to support
  //    that if not directly supported by ff.h
  //   What if the file create fails?
  //   What is the file write fails?
  
}

void write_entry_to_secure_log(const secure_log the_secure_log,
                               const log_entry a_log_entry) {

  // 0. Assume a_log_entry is already padded with zeroes
  
  // 1. Introduce a local (static, file-scope) variable previos_hash. Set it above in
  //    create_secure_log for the first time.
  
  // 2. Form the hash value from the message and previous_hash as per the Cryptol spec.

  // 3. Save the new hash to previous_hash

  // 4. Write the log_entry message to the_secure_log

  // 5. Write the hash block

  // 6. Sync the file.

  return;
}

