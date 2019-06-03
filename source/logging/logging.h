#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#define MESSAGE_MAX_LENGTH (256)
#define FILE_NAME "test_log.dat"
#define _SUCCESS  1
#define _FILE_ERROR -1
#define _IO_ERROR -2


typedef struct _LogEntry {
    unsigned int hash;
    char msg[MESSAGE_MAX_LENGTH];
   } LogEntry;

static char * _mode_append = "a";

static const char* _filename = FILE_NAME;

/*@ ghost const char* fileName=FILE_NAME;*/

/*@ ghost FILE * _fgh;*/

/*@ axiomatic AbstractRegion {
    logic char* abstract_region;
    axiom internal_state: abstract_region == _filename && 
          \separated(abstract_region, _filename);
 }
@*/

/*@
  predicate valid_le(LogEntry *le) = 
            \valid_read(le) &&
            \valid_read(((char*)(le -> msg))+(0 .. MESSAGE_MAX_LENGTH -1));
@*/

/*@
  predicate valid_input(LogEntry *le1, LogEntry *le2) =
            valid_le(le1) && valid_le(le2) &&
            \separated (((char*)(le1 -> msg))+(0 .. MESSAGE_MAX_LENGTH -1),
                       ((char*)(le2 -> msg))+(0 .. MESSAGE_MAX_LENGTH -1));
@*/

/*@
  predicate hash_equal(LogEntry *le1, LogEntry *le2) =
            le1 -> hash == le2 -> hash;
@*/

/*@ predicate is_null = _fgh ==\null;*/

/*@
  predicate is_separated(char *_filename)=
            \separated(&__fc_p_fopen,_filename+(..));
@*/

/*@ predicate is_subset= \subset(_fgh,&__fc_fopen[0 ..__FC_FOPEN_MAX-1]);*/

/*@
 predicate  valid_ptr_block(LogEntry *le)=
            \valid_read((char *)((void const *)le) +
                       (0 .. (unsigned int)1 * sizeof(LogEntry) - 1));
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
   requires valid_read_string(_filename);
   requires valid_read_string(_mode_append);
   assigns _fgh;
        ensures is_null ==> \result == _FILE_ERROR;
   ensures !is_null  && 
           is_subset && 
           is_separated(_filename) && 
           valid_ptr_block(le) ==> \result == _SUCCESS;
@*/
int write_entry(LogEntry *le);


/*@
   assigns fileName, *abstract_region, _filename;
   ensures val == fileName;
@*/
void set_log_file(char* val);
