/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes

// Subsystem includes
#include "secure_log.h"
#include "hsm.h"

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
  hmac (key, msg, LOG_ENTRY_LENGTH, &initial_entry.the_digest);

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

secure_log create_secure_log(const secure_log_name the_secure_log_name,
                             const log_entry a_log_entry_type,
                             const secure_log_security_policy the_policy)
{

  // Initial/Draft pseudo-code by RCC

  // 1. Create new file, open for writing only.
  // 2. call initial_log_entry above to create the first block
  // 3. Write that new block to the file.
  // 4. sync the file.
  // 5. return the file handle as result

  // TBDs - what about error cases?
  //   What if the file already exists? Perhaps a pre-condition here that it doesn't
  //    already exist, so up to the caller to spot that and do the right thing...
  //    We may have to implement an f_exists() API (and ACSL logic function) to support
  //    that if not directly supported by ff.h
  //   What if the file create fails?
  //   What is the file write fails?
  //
  // RCC I don't acually like the idea of leaving the file handle open all the time.
  //     Why not close it at the end of each operation? Does this grant more integrity on failure?
  
}

void write_entry_to_secure_log(const secure_log the_secure_log,
                               const log_entry a_log_entry) {
  // @example kiniry I wrote this example sketch implementation while
  // talking to Dragan about type refinement in C and the relationship
  // between the features of secure log and log.
     write_entry(the_secure_log, a_log_entry);
  // digest d = hash(the_last_digest, a_log_entry);
  // write(d, the_secure_log);
}

