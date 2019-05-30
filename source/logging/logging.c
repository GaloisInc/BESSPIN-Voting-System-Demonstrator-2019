#include <logging.h>
#include <stdio.h>
#include <stdlib.h>

bool hash_is_equal(LogEntry *le1, LogEntry *le2) {
    return (le1 -> hash == le2 -> hash)? true : false;
}


void set_log_file(char* val) {
  _filename = val;
 //@ ghost fileName = _filename;
 }

int write_entry(LogEntry *le) {
    FILE * _f = fopen (_filename, "a");
    if (_f == NULL)
    {
        return -1;
    }
    fwrite ((void *)le, sizeof(LogEntry), 1, _f);
    if(&fwrite == 0) {
        return -1;
    }
    fclose (_f);
    return 0;
}

