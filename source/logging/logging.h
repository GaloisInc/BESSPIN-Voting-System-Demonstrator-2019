#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#define MESSAGE_MAX_LENGTH (256)
#define _SUCCESS  1
#define _FILE_ERROR -1
#define _IO_ERROR -2

/** component LogEntry */
typedef struct _LogEntry {
    unsigned int hash;
    char msg[MESSAGE_MAX_LENGTH];
   } LogEntry;

/*@ ghost FILE * g_log;*/

/*@
  predicate is_valid_log_entry(LogEntry *le) = 
            \valid_read(le) &&
            \valid_read(((char*)(le -> msg))+(0 .. MESSAGE_MAX_LENGTH -1));
@*/

/*@
  predicate valid_log_entries(LogEntry *le1, LogEntry *le2) =
            is_valid_log_entry(le1) && is_valid_log_entry(le2) &&
            \separated (((char*)(le1 -> msg))+(0 .. MESSAGE_MAX_LENGTH -1),
                       ((char*)(le2 -> msg))+(0 .. MESSAGE_MAX_LENGTH -1));
@*/

/*@
  predicate hashes_are_equal(LogEntry *le1, LogEntry *le2) =
            le1 -> hash == le2 -> hash;
@*/

/*@ predicate is_null = g_log ==\null;*/

/*@
  predicate is_separated(char * _logname)=
            \separated(&__fc_p_fopen,_logname+(..));
@*/

/*@ predicate is_subset= \subset(g_log,&__fc_fopen[0 ..__FC_FOPEN_MAX-1]);*/

/*@
 predicate  valid_ptr_block(LogEntry *le)=
            \valid_read((char *)((void const *)le) +
                       (0 .. (unsigned int)1 * sizeof(LogEntry) - 1));
@*/


/*@
   requires is_valid_log_entry(le);
   requires valid_read_string(_logname);
   requires valid_read_string(_mode);
   assigns g_log;
        ensures is_null ==> \result == _FILE_ERROR;
   ensures !is_null  && is_subset && is_separated(_logname) && 
           valid_ptr_block(le) ==> \result == _SUCCESS;
@*/

/** component Log: Save this entry to the log!*/
int save_entry_to_log(LogEntry *le, char *_logname, char *_mode);

/**component Log: Read entry from the log!*/
int read_entry_from_the_log(char * _logname, int len); 

/*@
   requires valid_log_entries(le1, le2);
   ensures hashes_are_equal(le1, le2) ==> \result;
   ensures !hashes_are_equal(le1, le2) ==>!\result;
@*/
/**component HashChain: is_the_same_hash_code?*/
bool is_the_same_hash_code(LogEntry *le1, LogEntry *le2);
