#include <logging.h>

bool hash_is_equal(LogEntry *le1, LogEntry *le2) {
    return (le1 -> hash == le2 -> hash)? true : false;
}


void set_log_file(char* val) {
  _filename = val;
 //@ ghost fileName = _filename;
 }

int write_entry(LogEntry *le) {
    FILE * _f = fopen (_filename, _mode_append);
    //@ ghost _fgh = _f;
    if (_f == NULL)
    {
        return _FILE_ERROR;
    }
    fwrite (le, sizeof(LogEntry), 1, _f);
    if(&fwrite == 0) 
    {
        return _IO_ERROR;
    }
    fclose (_f);
    return _SUCCESS;
}

