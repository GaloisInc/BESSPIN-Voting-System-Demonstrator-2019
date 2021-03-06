/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes

// Subsystem includes
#include "logging/secure_log.h"
#include "logging/debug_io.h"
#include "crypto/crypto.h"

// Local constants

// Local persistent state

// Local functions


// Refines Cryptol initialLogEntry
#pragma GCC diagnostic ignored "-Waggregate-return"
/*@
    requires \valid_read (msg + (0 .. LOG_ENTRY_LENGTH - 1));
    assigns \nothing;
*/
static secure_log_entry initial_log_entry(const log_entry msg) // IN
{
    secure_log_entry initial_entry = {.the_entry = {0}, .the_digest = {0}};

    // 1. Zero-pad msg to exactly 256 chars with zeros.
    // log_entry is exactly 256 chars, so we'll assume this has already been
    // done by the caller.

    // 2. Form "aes_cbc_mac msg"
    // The MAC occupies the first 16 bytes of initial_entry.the_digest, while
    // the remaining bytes are all 0x00 as initialized above.
    aes_cbc_mac((message)msg, LOG_ENTRY_LENGTH, &initial_entry.the_digest[0], Log_Root_Block_MAC_Key);

    // 3. Copy the msg data
    copy_log_entry (&initial_entry.the_entry[0], &msg[0]);

    return initial_entry; // struct by copy return
}

// Exported functions

Log_FS_Result create_secure_log(Log_Handle *new_secure_log,
                                const secure_log_name the_secure_log_name,
                                const log_entry a_log_entry_type,
                                const secure_log_security_policy the_policy,
                                const http_endpoint endpoint)
{
    (void)the_policy;
    Log_FS_Result create_result, write_result, sync_result;
    secure_log_entry initial_entry;

    // Initial/Draft pseudo-code by RCC

    // 1. Create new file, open for writing only.
    create_result = Log_IO_Create_New(new_secure_log, the_secure_log_name, endpoint);

    if (create_result == LOG_FS_OK) 
      {
        // 2. call initial_log_entry above to create the first block
        initial_entry = initial_log_entry(a_log_entry_type);

        // keep the first hash
        copy_sha256_digest (&new_secure_log->previous_hash[0],
                &initial_entry.the_digest[0]);

        // 3. Write that new block to the file.
        write_result = Log_IO_Write_Base64_Entry(new_secure_log, initial_entry);

        // 4. sync the file.
        sync_result = Log_IO_Sync(new_secure_log);

        // TBDs - what about error cases?
        //   What if the file already exists? Perhaps a pre-condition here that it doesn't
        //    already exist, so up to the caller to spot that and do the right thing...
        //    We may have to implement an f_exists() API (and ACSL logic function) to support
        //    that if not directly supported by ff.h
        //   What if the file create fails?
        //   What is the file write fails?
        (void)sync_result;
        (void)write_result;
        return LOG_FS_OK;
      }
    else
      {
	return LOG_FS_ERROR;
      }
    
}

Log_FS_Result write_entry_to_secure_log(const secure_log the_secure_log,
                                        const log_entry a_log_entry)
{
    Log_FS_Result write_result, sync_result;
    secure_log_entry current_entry;
    sha256_digest new_hash;
    uint8_t msg[SECURE_LOG_ENTRY_LENGTH]; // appended message

    // Assume a_log_entry is already padded with zeroes

    // compute new_hash = hash (a_log_entry # previousHash)
    copy_log_entry (&msg[0], &a_log_entry[0]);
    copy_sha256_digest (&msg[LOG_ENTRY_LENGTH], &the_secure_log->previous_hash[0]);
    hash(msg, SECURE_LOG_ENTRY_LENGTH, &new_hash[0]);

    // current_entry = (a_log_entry # new_hash)
    copy_log_entry (&current_entry.the_entry[0], &a_log_entry[0]);
    copy_sha256_digest (&current_entry.the_digest[0], &new_hash[0]);

    // Write the new block
    write_result = Log_IO_Write_Base64_Entry(the_secure_log, current_entry);

    // Sync the file.
    sync_result = Log_IO_Sync(the_secure_log);

    // Save the new hash to previous_hash and
    copy_sha256_digest (&the_secure_log->previous_hash[0], &new_hash[0]);

    (void)write_result;
    (void)sync_result;
    return LOG_FS_OK;
}

// Refinces Cryptol validFirstEntry
bool valid_first_entry(secure_log_entry root_entry)
{
    sha256_digest new_mac = {0};

    // 2. Form the AES CBC MAC of the message part of root_entry
    aes_cbc_mac(root_entry.the_entry, LOG_ENTRY_LENGTH, &new_mac[0], Log_Root_Block_MAC_Key);

    // 3. new_mac and root_entry.the_digest should match, but only
    //    comparing the first AES_BLOCK_LENGTH_BYTES which are
    //    significant
    /*@
      loop invariant 0 <= i <= AES_BLOCK_LENGTH_BYTES;
      loop assigns i;
      loop variant AES_BLOCK_LENGTH_BYTES - i;
     */
    for (int i = 0; i < AES_BLOCK_LENGTH_BYTES; i++)
    {
        if (root_entry.the_digest[i] != new_mac[i])
        {
          debug_printf ("valid_first_entry - MACs do not match");
          return false;
        }
    }
    debug_printf ("valid_first_entry - MACs match OK");
    return true;
}

// Refinces Cryptol validLogEntry
/*@
  requires \valid_read(prev_hash + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
*/
bool valid_log_entry(const secure_log_entry this_entry,
                     const sha256_digest prev_hash)
{
    uint8_t msg[SECURE_LOG_ENTRY_LENGTH];
    sha256_digest new_hash = {0};

    // Concatenate this_entry and prev_hash into msg and hash it
    copy_log_entry (&msg[0], &this_entry.the_entry[0]);
    copy_sha256_digest (&msg[LOG_ENTRY_LENGTH], &prev_hash[0]);
    hash(msg, SECURE_LOG_ENTRY_LENGTH, &new_hash[0]);

    // new_hash and this_entry.the_digest should match
    /*@
      loop invariant 0 <= i <= SHA256_DIGEST_LENGTH_BYTES;
      loop assigns i;
      loop variant SHA256_DIGEST_LENGTH_BYTES - i;
    */
    for (int i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
        if (this_entry.the_digest[i] != new_hash[i])
        {
            debug_printf ("valid_log_entry - hashes do not match");
            return false;
        }
    }
    debug_printf ("valid_log_entry - hashes match OK");
    return true;
}

// Refines Cryptol validLogFile
bool verify_secure_log_security(secure_log the_secure_log)
{
    // A log file is valid if the first (root) entry is valid AND
    // all the subsequent entries are valid.
    secure_log_entry root_entry = {.the_entry = {0}, .the_digest = {0}};
    sha256_digest prev_hash;
    secure_log_entry this_entry;
    size_t num_entries;

    num_entries = Log_IO_Num_Base64_Entries(the_secure_log);
    switch (num_entries)
      {
      case 0:
        // Apparently zero entries... something must be wrong, so
        return false;
        break;
      case 1:
        debug_printf ("valid_secure_log_security - checking only entry MAC");

        // Fetch the root entry
        root_entry = Log_IO_Read_Base64_Entry(the_secure_log, 0);

        if (valid_first_entry(root_entry))
          {
            // If all is well, then save the hash of the root entry for later,
            // additional entries to use.

            // whole array assignment  the_secure_log->previous_hash = root_entry.the_digest;
            copy_sha256_digest (&the_secure_log->previous_hash[0],
                                &root_entry.the_digest[0]);
            return true;
          }
        else
          {
            return false;
          }
        break;

      default:

        debug_printf ("valid_secure_log_security - checking first entry MAC");

        // Fetch the root entry
        root_entry = Log_IO_Read_Base64_Entry(the_secure_log, 0);

        if (valid_first_entry(root_entry))
          {
            // If all is well, then save the hash of the root entry to verify
            // the next one.
            // whole array assignment  prev_hash = root_entry.the_digest;
            copy_sha256_digest(&prev_hash[0], &root_entry.the_digest[0]);

            /*@
              loop invariant 2 <= i <= (num_entries + 1);
              loop assigns this_entry, *prev_hash;
              loop variant num_entries - i;
            */
            for (size_t i = 2; i <= num_entries; i++)
              {
                // In the file, entries are numbered starting at 0, so we want the
                // (i - 1)'th entry...
                this_entry = Log_IO_Read_Base64_Entry(the_secure_log, (i - 1));

                debug_printf ("valid_secure_log_security - checking validity of entry %zu", i);

                if (valid_log_entry(this_entry, prev_hash))
                  {
                    // whole array assignment  prev_hash = this_entry.the_digest;
                    copy_sha256_digest(&prev_hash[0], &this_entry.the_digest[0]);
                  }
                else
                  {
                    return false;
                  }
              }

            // All entries are OK if we've reached this point, so save the
            // final hash into the_secure_log->previous_hash so that more
            // entries can be appended later.
            //
            // whole array assignment  the_secure_log->previous_hash = prev_hash;
            copy_sha256_digest(&the_secure_log->previous_hash[0], &prev_hash[0]);

            return true;
          }
        else
          {
            // First entry is not valid, so
            return false;
          }

        break;

      }
}
