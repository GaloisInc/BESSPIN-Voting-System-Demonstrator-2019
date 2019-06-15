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

// Local persistent state

static sha256_digest previous_hash;

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

  // 2.1 @dragan keep the first hash
     /*@
      loop invariant 0 <= i <= SHA256_DIGEST_LENGTH_BYTES;
      loop invariant \forall size_t k; 0 <= k < i ==> previous_hash[k] == initial_entry.the_digest[k];
      loop assigns previous_hash[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
      loop variant SHA256_DIGEST_LENGTH_BYTES - i;
  */
    for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      previous_hash[i] = initial_entry.the_digest[i];
    }

  // 3. Write that new block to the file.
  write_result = Log_IO_Write_Entry (secure_log, initial_entry);

  // TBD - what to do with the_policy parameter?
  //       awaiting requirements on this.
  
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

  Log_FS_Result write_result, sync_result;
  secure_log_entry current_entry;
  sha256_digest new_hash;
  uint8_t msg[SECURE_LOG_ENTRY_LENGTH]; // appended message
  size_t index=0;


  // 0. Assume a_log_entry is already padded with zeroes

  // 1. Introduce a local (static, file-scope) variable previous_hash. Set it above in
  //    create_secure_log for the first time.

  // 2. Form the hash value from the message and previous_hash as per the Cryptol spec.
  // hash (paddedMsg # previousHash) is secure_log_entry I guess.
  // adding padded a_log_entry

  /*@
      loop invariant 0 <= i <= LOG_ENTRY_LENGTH;
      loop invariant \forall size_t j, index; (0 <= j < i) && (index ==j)  ==> msg[index] == a_log_entry[j];
      loop assigns i, index, msg[0 .. LOG_ENTRY_LENGTH - 1];
      loop variant LOG_ENTRY_LENGTH - i;
  */
  for (size_t i = 0; i < LOG_ENTRY_LENGTH; i++)
    {
      msg[index] = a_log_entry[i];
      index++;
    }

  // adding previous_hash
/*@
      loop invariant 0 <= i <= SHA256_DIGEST_LENGTH_BYTES;
      loop invariant \forall size_t j, index; (0 <= j < i) && (index ==j)  ==> msg[index] == a_log_entry[j];
      loop assigns i, index, msg[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
      loop variant SHA256_DIGEST_LENGTH_BYTES - i;
  */
   for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      msg[index] = previous_hash[i];
      index++;
    }

   // invoke hash ( paddedMsg # previousHash)
   sha256 (msg,SECURE_LOG_ENTRY_LENGTH, &new_hash[0]);
   
   // Add the a_log_entry to the current_entry
   /*@
      loop invariant 0 <= i <= LOG_ENTRY_LENGTH;
      loop invariant \forall size_t j; 0 <= j < i ==> current_entry.the_entry[j] == a_log_entry[j];
      loop assigns i, current_entry.the_entry[0 .. LOG_ENTRY_LENGTH - 1];
      loop variant LOG_ENTRY_LENGTH - i;
  */
   for (size_t i = 0; i < LOG_ENTRY_LENGTH; i++)
     {
       current_entry.the_entry[i] = a_log_entry[i];
     }
   
   // 3. Save the new hash to previous_hash and
   //    copy new_hash into the current_entry
     /*@
      loop invariant 0 <= i <= SHA256_DIGEST_LENGTH_BYTES;
      loop invariant \forall size_t j; 0 <= j < i ==> current_entry.the_digest[j] == new_hash[j];
      loop invariant \forall size_t k; 0 <= k < i ==> previous_hash[k] == new_hash[k];
      loop assigns i, current_entry.the_digest[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
      loop assigns previous_hash[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
      loop variant SHA256_DIGEST_LENGTH_BYTES - i;
  */
   for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
     {
       current_entry.the_digest[i] = new_hash[i];
       previous_hash[i]            = new_hash[i];
     }
   
   // 4. Write the log_entry message to the_secure_log
   
   write_result = Log_IO_Write_Entry (the_secure_log, current_entry);
   
   // 5. Write the hash block
   
   // 6. Sync the file.
   sync_result = Log_IO_Sync (the_secure_log);
   
   return;
}

// Refinces Cryptol validFirstEntry
bool valid_first_entry (const secure_log the_secure_log)
{
  const aes256_key dummy_key = {0};
  sha256_digest new_hmac = {0};
  secure_log_entry root_entry;

  // 1. Fetch the root block from the file
  root_entry = Log_IO_Read_Entry (the_secure_log, 0);  

  // 2. Form "hmac key log.msg"
  hmac (dummy_key, root_entry.the_entry, LOG_ENTRY_LENGTH, &new_hmac[0]);

  // 3. new_hmac and root_entry.the_digest should match
  for (int i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      if (root_entry.the_digest[i] != new_hmac[i])
	{
	  return false;
	}
    }
  return true;

}

// Refinces Cryptol validLogEntry
bool valid_log_entry (const secure_log_entry this_entry,
		      const sha256_digest    prev_hash)
{
  uint8_t msg[SECURE_LOG_ENTRY_LENGTH];
  size_t index = 0;
  sha256_digest new_hash = {0};

  // Concatenate this_entry and prev_hash into msg
  for (size_t i = 0; i < LOG_ENTRY_LENGTH; i++)
    {
      msg[index] = this_entry.the_entry[i];
      index++;
    }
  
  for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      msg[index] = prev_hash[i];
      index++;
    }
  
  sha256 (msg, SECURE_LOG_ENTRY_LENGTH, &new_hash[0]);
  
  // 3. new_hash and this_entry.the_digest should match
  for (int i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      if (this_entry.the_digest[i] != new_hash[i])
	{
	  return false;
	}
    }
  return true;
}


// Refines Cryptol validLogFile
bool verify_secure_log_security(const secure_log the_secure_log)
{
  // A log file is valid if the first (root) entry is valid AND
  // all the subsequent entries are valid.
  secure_log_entry root_entry;
  sha256_digest    prev_hash;
  secure_log_entry this_entry;

  if (valid_first_entry (the_secure_log))
    {
      size_t num_entries;
      num_entries = Log_IO_Num_Entries (the_secure_log);
      switch (num_entries)
	{
	case 0:
	  // a valid first entry, but apparently zero entries... something
	  // must be wrong, so
	  return false;
	  break;
	case 1:
	  // One entry must be the first entry and we already know it's OK, so
	  return true;
	  break;

	default:
	  // Fetch the root entry and keep a copy of it Hash in prev_hash
	  root_entry = Log_IO_Read_Entry (the_secure_log, 0);  

	  // whole array assignment  prev_hash = root_entry.the_digest;
	  memcpy (&prev_hash[0], &root_entry.the_digest[0], SHA256_DIGEST_LENGTH_BYTES);
	  
	  // Two or more entries
	  for (size_t i = 2; i <= num_entries; i++)
	    {
	      // In the file, entries are numbered starting at 0, so we want the
	      // (i - 1)'th entry...
	      this_entry = Log_IO_Read_Entry (the_secure_log, (i - 1));
	      
              if (valid_log_entry (this_entry, prev_hash))
		{
		  // whole array assignment  prev_hash = this_entry.the_digest;
		  memcpy (&prev_hash[0],
			  &this_entry.the_digest[0],
			  SHA256_DIGEST_LENGTH_BYTES);
		}
	      else
		{
		  return false;
		}
	    }
	  // Loop must have successfully verified all entries, so
	  return true;
	  break;
	}
      
    }
  else
    {
      // First block is invalid, so
      return false;
    }
}
