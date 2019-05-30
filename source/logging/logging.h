#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#define MESSAGE_MAX_LENGTH (256)
#define FILE_NAME "test_log.dat"

typedef struct _LogEntry {
    unsigned int hash;
    char msg[MESSAGE_MAX_LENGTH];
   } LogEntry;

static const char* _filename = FILE_NAME;

//@ ghost const char* fileName=FILE_NAME;

/*@ axiomatic AbstractRegion {
    
    logic char* abstract_region;
    axiom internal_state: abstract_region == _filename;
 }
@*/

/*@
  predicate valid_le(LogEntry *le) = 
    \valid_read(le) &&
    \valid_read(((char*)(le -> msg))+(0 .. MESSAGE_MAX_LENGTH -1));

  predicate valid_input(LogEntry *le1, LogEntry *le2) =
     valid_le(le1) && valid_le(le2) &&
     \separated (((char*)(le1 -> msg))+(0 .. MESSAGE_MAX_LENGTH -1),
      ((char*)(le2 -> msg))+(0 .. MESSAGE_MAX_LENGTH -1));

  predicate hash_equal(LogEntry *le1, LogEntry *le2) =
     le1 -> hash == le2 -> hash;
@*/

/*@
   requires valid_input(le1, le2);
   behavior hash_equal:
        assumes hash_equal(le1, le2);
        ensures \result;
   behavior hash_non_equal:
        assumes !hash_equal(le1, le2);
        ensures !\result;
   complete behaviors;
   disjoint behaviors;
@*/
bool hash_is_equal(LogEntry *le1, LogEntry *le2);


/*@
   requires valid_le(le);
   requires valid_read_string(fileName);
   ensures result_ok_or_error: \result == 0 || \result == -1;
@*/
int write_entry(LogEntry *le);

/*@
// assignement still in unknown state ?
   assigns fileName, *abstract_region;
   assigns _filename;
   ensures val == fileName;
@*/
void set_log_file(char* val);
