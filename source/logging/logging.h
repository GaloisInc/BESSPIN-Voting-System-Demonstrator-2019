#include <stdbool.h>
#include <stdio.h>
#include"__fc_builtin.h"
#include <stdlib.h>
#include"__fc_string_axiomatic.h"
#define MESSAGE_MAX_LENGTH 256


typedef struct _LogEntry {
    unsigned int hash;
    char msg[MESSAGE_MAX_LENGTH];
   } LogEntry;



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
@*/
// check if hash is equal 
bool hash_is_equal(LogEntry *le1, LogEntry *le2);

// write an entry into log file.
int write_entry(LogEntry *le);
